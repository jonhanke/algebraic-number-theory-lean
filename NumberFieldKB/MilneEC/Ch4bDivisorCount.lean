import NumberFieldKB.MilneEC.Ch4bRiemannRoch
import NumberFieldKB.MilneEC.Ch4bZetaEuler

/-!
# Milne, Elliptic Curves, Chapter IV §9: Proposition 9.9 and Theorem 9.10

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 9.9 and Theorem 9.10,
pdf pp. 162–163.

**Proposition 9.9**: an elliptic curve $E$ over $\mathbb F_p$ has exactly $N_1 (p^m - 1)/(p - 1)$ positive divisors of
degree $m \ge 1$, $N_1 = \#E(\mathbb F_p)$.

**Milne's proof, transposed to the affine coordinate ring** $R = \mathbb F_p[x, y]$ (a Dedekind domain).  A positive
divisor of degree $m$ is $D + nO$ with $D$ a positive divisor on the affine part, so the count is the number of
positive affine divisors of degree at most $m$, i.e. (unique factorization of ideals) of nonzero ideals $I$ of $R$ with
$\dim R/I \le m$ (`posDivCount_eq_card_ideals`).  Group them by ideal class.  For the class $c$, fix a nonzero ideal $J$ in the
inverse class; the ideals $I$ of class $c$ are the $I$ with $IJ = (f)$, $f \in J$, determined by $f$ up to a unit, i.e.
a nonzero constant; and $\dim R/I = \operatorname{wt}(f) - \dim R/J$.  So their number is
$(\#\{f \in J : \operatorname{wt}(f) \le m + \dim R/J\} - 1)/(p - 1) = (p^m - 1)/(p - 1)$ by Riemann–Roch
(`card_inf_Vn`): Milne's
"$\#\{D' \ge 0, D' \sim D\} = (p^{\ell(D)} - 1)/(p - 1)$, $\ell(D) = m$".  The number of classes is
$\#\operatorname{Pic}^0(E) = \#E(\mathbb F_p) = N_1$ (`WeierstrassCurve.Affine.Point.toClassEquiv`).

## Main results
* `card_ideals_in_class`: $(p - 1)\cdot\#\{I : [I] = c, \dim R/I \le m\} = p^m - 1$.
* `prop9_9`: the named statement `Prop9_9` holds.
* `theorem_9_10_unconditional`: Theorem 9.10, $Z(E, T) = \dfrac{1 + (N_1 - p - 1)T + pT^2}{(1 - T)(1 - pT)}$.
* `remark_9_11_a_unconditional`: $N_m = 1 + p^m - \alpha^m - \beta^m$.
-/

open Polynomial WeierstrassCurve

namespace NumberFieldKB.MilneEC

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]

/-- The ideal $\prod_{\mathfrak p} \mathfrak p^{D(\mathfrak p)}$ of a positive affine divisor $D$. -/
noncomputable def divIdeal (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) :
    Ideal W.toAffine.CoordinateRing :=
  D.prod fun 𝔭 n => 𝔭.asIdeal ^ n

/-- The coordinate ring is not a field. -/
private theorem not_isField_coordinateRing : ¬ IsField W.toAffine.CoordinateRing := by
  intro hF
  have hX : algebraMap (ZMod p)[X] W.toAffine.CoordinateRing Polynomial.X ≠ 0 := by
    intro h
    have := (FaithfulSMul.algebraMap_injective (ZMod p)[X] W.toAffine.CoordinateRing)
      (h.trans (map_zero _).symm)
    exact Polynomial.X_ne_zero this
  have hu : IsUnit (algebraMap (ZMod p)[X] W.toAffine.CoordinateRing Polynomial.X) :=
    (let ⟨b, hb⟩ := hF.mul_inv_cancel hX; isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
  obtain ⟨c, _, hc⟩ := exists_const_of_isUnit W hu
  rw [IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)[X] W.toAffine.CoordinateRing,
    Polynomial.algebraMap_eq] at hc
  have := (FaithfulSMul.algebraMap_injective (ZMod p)[X] W.toAffine.CoordinateRing) hc
  exact Polynomial.X_ne_C c this

/-- A maximal ideal of the coordinate ring is nonzero. -/
private theorem asIdeal_ne_bot (𝔭 : MaximalSpectrum W.toAffine.CoordinateRing) : 𝔭.asIdeal ≠ ⊥ := by
  have := Ideal.bot_lt_of_maximal 𝔭.asIdeal (not_isField_coordinateRing W)
  exact bot_lt_iff_ne_bot.mp this

/-- The codimension of $\mathfrak p^n$. -/
private theorem codim_pow (𝔭 : MaximalSpectrum W.toAffine.CoordinateRing) (n : ℕ) :
    codim W (𝔭.asIdeal ^ n) = n * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭 := by
  induction n with
  | zero =>
    have hsub : Subsingleton (W.toAffine.CoordinateRing ⧸ (𝔭.asIdeal ^ 0)) := by
      rw [pow_zero, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    simpa [codim] using Module.finrank_zero_of_subsingleton (R := ZMod p)
      (M := W.toAffine.CoordinateRing ⧸ (𝔭.asIdeal ^ 0))
  | succ n ih =>
    rw [pow_succ, codim_mul W _ _ (pow_ne_zero _ (asIdeal_ne_bot W 𝔭)) (asIdeal_ne_bot W 𝔭), ih]
    simp only [maxDeg, codim]
    ring

/-- A finite product of powers of maximal ideals is nonzero. -/
private theorem prod_pow_ne_bot (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ)
    (s : Finset (MaximalSpectrum W.toAffine.CoordinateRing)) :
    ∏ 𝔭 ∈ s, 𝔭.asIdeal ^ (D 𝔭) ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_ne_zero (pow_ne_zero _ (asIdeal_ne_bot W a)) ih

/-- Codimension of a finite product of powers of maximal ideals. -/
private theorem codim_prod_pow (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ)
    (s : Finset (MaximalSpectrum W.toAffine.CoordinateRing)) :
    codim W (∏ 𝔭 ∈ s, 𝔭.asIdeal ^ (D 𝔭)) =
      ∑ 𝔭 ∈ s, D 𝔭 * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hsub : Subsingleton (W.toAffine.CoordinateRing ⧸
        (∏ 𝔭 ∈ (∅ : Finset (MaximalSpectrum W.toAffine.CoordinateRing)), 𝔭.asIdeal ^ (D 𝔭))) := by
      rw [Finset.prod_empty, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    simpa [codim] using Module.finrank_zero_of_subsingleton (R := ZMod p)
      (M := W.toAffine.CoordinateRing ⧸
        (∏ 𝔭 ∈ (∅ : Finset (MaximalSpectrum W.toAffine.CoordinateRing)), 𝔭.asIdeal ^ (D 𝔭)))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      codim_mul W _ _ (pow_ne_zero _ (asIdeal_ne_bot W a)) (prod_pow_ne_bot W D s), ih, codim_pow]

/-- The codimension of $\prod \mathfrak p^{D(\mathfrak p)}$ is the degree $\sum D(\mathfrak p) \deg \mathfrak p$. -/
theorem codim_divIdeal (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) :
    codim W (divIdeal W D) = D.sum (fun 𝔭 n => n * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭) :=
  codim_prod_pow W D D.support

theorem divIdeal_ne_bot (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) : divIdeal W D ≠ ⊥ :=
  prod_pow_ne_bot W D D.support

/-- `divIdeal` as the product of a multiset of maximal ideals. -/
private theorem divIdeal_eq_multiset_prod (D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) :
    divIdeal W D = ((Finsupp.toMultiset D).map (fun 𝔭 => 𝔭.asIdeal)).prod := by
  induction D using Finsupp.induction_linear with
  | zero => simp [divIdeal]
  | add f g hf hg =>
    rw [divIdeal, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ← divIdeal, ← divIdeal,
      hf, hg, map_add, Multiset.map_add, Multiset.prod_add]
  | single a n =>
    rw [divIdeal, Finsupp.prod_single_index (by simp), Finsupp.toMultiset_single, Multiset.map_nsmul,
      Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton]

/-- Unique factorization of ideals: $D \mapsto \prod \mathfrak p^{D(\mathfrak p)}$ is injective. -/
theorem divIdeal_injective : Function.Injective (divIdeal W) := by
  classical
  intro D₁ D₂ h
  have hprime : ∀ D : MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ,
      ∀ q ∈ (Finsupp.toMultiset D).map (fun 𝔭 => 𝔭.asIdeal), Prime q := by
    intro D q hq
    obtain ⟨𝔭, -, rfl⟩ := Multiset.mem_map.mp hq
    exact Ideal.prime_of_isPrime (asIdeal_ne_bot W 𝔭) 𝔭.isMaximal.isPrime
  rw [divIdeal_eq_multiset_prod, divIdeal_eq_multiset_prod] at h
  have h2 := congrArg UniqueFactorizationMonoid.normalizedFactors h
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (hprime D₁),
    UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (hprime D₂)] at h2
  exact Function.LeftInverse.injective (g := Multiset.toFinsupp)
    (fun D => Multiset.toFinsupp_eq_iff.mpr rfl)
    (Multiset.map_injective (fun a b hab => MaximalSpectrum.ext hab) h2)

/-- Unique factorization of ideals: every nonzero ideal is $\prod \mathfrak p^{D(\mathfrak p)}$ for a positive affine divisor $D$. -/
theorem exists_divIdeal_eq (I : Ideal W.toAffine.CoordinateRing) (hI : I ≠ ⊥) :
    ∃ D, divIdeal W D = I := by
  classical
  have key : ∀ s : Multiset (Ideal W.toAffine.CoordinateRing), (∀ q ∈ s, q.IsMaximal) →
      ∃ m : Multiset (MaximalSpectrum W.toAffine.CoordinateRing), m.map (fun 𝔭 => 𝔭.asIdeal) = s := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | cons q s ih =>
      intro h
      obtain ⟨m, hm⟩ := ih (fun q hq => h q (Multiset.mem_cons_of_mem hq))
      exact ⟨(⟨q, h q (Multiset.mem_cons_self _ _)⟩ : MaximalSpectrum _) ::ₘ m, by simp [hm]⟩
  obtain ⟨m, hm⟩ := key (UniqueFactorizationMonoid.normalizedFactors I) (fun q hq => by
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
    exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero)
  refine ⟨Multiset.toFinsupp m, ?_⟩
  rw [divIdeal_eq_multiset_prod, Multiset.toFinsupp_toMultiset, hm,
    Ideal.prod_normalizedFactors_eq_self hI]

/-- The number of positive divisors of degree $m$ on $E$ is the number of nonzero ideals of $R$ of codimension at
most $m$. -/
theorem posDivCount_eq_card_ideals (m : ℕ) :
    posDivCount W m = Nat.card {I : Ideal W.toAffine.CoordinateRing // I ≠ ⊥ ∧ codim W I ≤ m} := by
  let F : {x : (MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) × ℕ //
      x.1.sum (fun 𝔭 n => n * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭) + x.2 = m} →
      {I : Ideal W.toAffine.CoordinateRing // I ≠ ⊥ ∧ codim W I ≤ m} :=
    fun x => ⟨divIdeal W x.1.1, divIdeal_ne_bot W x.1.1, by
      rw [codim_divIdeal]; have := x.2; omega⟩
  have hinj : Function.Injective F := by
    intro x y h
    have h1 : x.1.1 = y.1.1 := divIdeal_injective W (congrArg Subtype.val h)
    have hx := x.2
    have hy := y.2
    refine Subtype.ext (Prod.ext h1 ?_)
    rw [← h1] at hy
    omega
  have hsurj : Function.Surjective F := by
    rintro ⟨I, hI, hc⟩
    obtain ⟨D, rfl⟩ := exists_divIdeal_eq W I hI
    rw [codim_divIdeal] at hc
    exact ⟨⟨(D, m - D.sum (fun 𝔭 n => n * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭)), by
      simp only; omega⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)

/-- The codimension of a principal ideal is the weight of its generator. -/
private theorem codim_span {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    codim W (Ideal.span {f}) = wt W f := by
  have hne : (Ideal.span {f} : Ideal W.toAffine.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have h1 := card_quotient_span W hf
  rw [card_quotient W _ hne] at h1
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1

/-- Generators of equal principal ideals differ by a nonzero constant. -/
private theorem exists_const_mul_of_span_eq {f g : W.toAffine.CoordinateRing}
    (h : Ideal.span {f} = (Ideal.span {g} : Ideal W.toAffine.CoordinateRing)) :
    ∃ u : ZMod p, u ≠ 0 ∧ g = algebraMap (ZMod p) W.toAffine.CoordinateRing u * f := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  obtain ⟨u, hu, hu'⟩ := exists_const_of_isUnit W v.isUnit
  refine ⟨u, hu, ?_⟩
  rw [← hv, ← hu', mul_comm]

/-- A nonzero constant is a unit of weight zero. -/
private theorem isUnit_algebraMap {u : ZMod p} (hu : u ≠ 0) :
    IsUnit (algebraMap (ZMod p) W.toAffine.CoordinateRing u) :=
  (isUnit_iff_ne_zero.mpr hu).map _

/-- Counting nonzero elements of a finite type with zero. -/
private theorem natCard_ne_zero_add_one (X : Type*) [Zero X] [Finite X] :
    Nat.card {x : X // x ≠ 0} + 1 = Nat.card X := by
  classical
  haveI := Fintype.ofFinite X
  have := Fintype.card_congr (Equiv.optionSubtypeNe (0 : X))
  rw [Fintype.card_option] at this
  simpa [Nat.card_eq_fintype_card] using this

/-- The cardinality of the units of the residue field `ZMod p` as nonzero elements is `p - 1`. -/
private theorem natCard_zmod_ne_zero : Nat.card {u : ZMod p // u ≠ 0} = p - 1 := by
  have := natCard_ne_zero_add_one (ZMod p)
  rw [Nat.card_zmod] at this
  omega

/-- **The divisors in one class** (Milne, pdf p. 162): for each ideal class $c$ and $m \ge 1$,
$(p - 1)\cdot\#\{I \neq 0 : [I] = c,\ \dim R/I \le m\} = p^m - 1$. -/
theorem card_ideals_in_class (c : ClassGroup W.toAffine.CoordinateRing) (m : ℕ) (hm : 1 ≤ m) :
    Nat.card {I : Ideal W.toAffine.CoordinateRing // ∃ hI : I ≠ ⊥, codim W I ≤ m ∧
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = c} * (p - 1) = p ^ m - 1 := by
  classical
  obtain ⟨⟨J, hJ'⟩, hJc⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ'
  -- the type of target ideals and of nonzero functions
  let T := {I : Ideal W.toAffine.CoordinateRing // ∃ hI : I ≠ ⊥, codim W I ≤ m ∧
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = c}
  let S := ↥(J.restrictScalars (ZMod p) ⊓ Vn W (m + codim W J))
  have hS : Nat.card S = p ^ m := by
    have := card_inf_Vn W J hJ (m + codim W J) (by omega)
    rw [show m + codim W J - codim W J = m by omega] at this
    exact this
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hA : Nat.card {f : S // f ≠ 0} = p ^ m - 1 := by
    have := natCard_ne_zero_add_one S
    omega
  -- generators for the ideals of `T`
  have hgen : ∀ I : T, ∃ g : W.toAffine.CoordinateRing, g ≠ 0 ∧ I.1 * J = Ideal.span {g} ∧
      g ∈ J ∧ wt W g ≤ m + codim W J := by
    rintro ⟨I, hI, hcod, hcl⟩
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    have h1 : ClassGroup.mk0 ⟨I * J, mem_nonZeroDivisors_of_ne_zero hIJ⟩ = 1 := by
      have : ClassGroup.mk0 (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ * ⟨J, hJ'⟩) = 1 := by
        rw [map_mul, hcl, hJc, mul_inv_cancel]
      exact this
    have hpr : (I * J).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hIJ)).mp h1
    obtain ⟨g, hg⟩ := hpr.principal
    have hg' : I * J = Ideal.span {g} := hg
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hIJ
      rw [hg']; simp
    refine ⟨g, hg0, hg', ?_, ?_⟩
    · have : g ∈ I * J := by rw [hg']; exact Ideal.mem_span_singleton_self g
      exact (Ideal.mul_le_right : I * J ≤ J) this
    · have := codim_mul W I J hI hJ
      rw [hg', codim_span W hg0] at this
      omega
  choose g hg0 hgI hgJ hgw using hgen
  have hu0 : ∀ u : ZMod p, u ≠ 0 → algebraMap (ZMod p) W.toAffine.CoordinateRing u ≠ 0 :=
    fun u hu => (isUnit_algebraMap W hu).ne_zero
  have hmem : ∀ (I : T) (u : ZMod p), u ≠ 0 →
      algebraMap (ZMod p) W.toAffine.CoordinateRing u * g I ∈
        J.restrictScalars (ZMod p) ⊓ Vn W (m + codim W J) := by
    intro I u hu
    refine ⟨Ideal.mul_mem_left J _ (hgJ I), ?_⟩
    refine (mem_Vn_iff W _ _).mpr (Or.inr ?_)
    rw [wt_mul W (hu0 u hu) (hg0 I), (isUnit_iff_wt_eq_zero W (hu0 u hu)).mp (isUnit_algebraMap W hu)]
    simpa using hgw I
  let F : T × {u : ZMod p // u ≠ 0} → {f : S // f ≠ 0} := fun x =>
    ⟨⟨algebraMap (ZMod p) W.toAffine.CoordinateRing x.2.1 * g x.1, hmem x.1 x.2.1 x.2.2⟩,
      fun h => mul_ne_zero (hu0 _ x.2.2) (hg0 x.1) (by simpa using congrArg Subtype.val h)⟩
  have hFval : ∀ x, (F x).1.1 = algebraMap (ZMod p) W.toAffine.CoordinateRing x.2.1 * g x.1 :=
    fun x => rfl
  have hinj : Function.Injective F := by
    rintro ⟨⟨I, hI⟩, ⟨u, hu⟩⟩ ⟨⟨I', hI'⟩, ⟨u', hu'⟩⟩ h
    have h1 := congrArg (fun z => z.1.1) h
    simp only [hFval] at h1
    have h2 : Ideal.span {g ⟨I, hI⟩} = Ideal.span {g ⟨I', hI'⟩} := by
      rw [← Ideal.span_singleton_mul_left_unit (isUnit_algebraMap W hu) (g ⟨I, hI⟩),
        ← Ideal.span_singleton_mul_left_unit (isUnit_algebraMap W hu') (g ⟨I', hI'⟩)]
      simpa only using congrArg (fun z => (Ideal.span {z} : Ideal W.toAffine.CoordinateRing)) h1
    have h3 : I * J = I' * J := by
      have := hgI ⟨I, hI⟩
      have := hgI ⟨I', hI'⟩
      simp only at *
      rw [‹I * J = _›, ‹I' * J = _›, h2]
    have h4 : I = I' := mul_right_cancel₀ hJ h3
    subst h4
    have h5 := mul_right_cancel₀ (hg0 ⟨I, hI⟩) h1
    have h6 := (FaithfulSMul.algebraMap_injective (ZMod p) W.toAffine.CoordinateRing) h5
    subst h6
    rfl
  have hsurj : Function.Surjective F := by
    rintro ⟨⟨f, hf⟩, hf0'⟩
    have hf0 : f ≠ 0 := fun h => hf0' (Subtype.ext h)
    have hfJ : f ∈ J := hf.1
    have hfw : wt W f ≤ m + codim W J := ((mem_Vn_iff W _ f).mp hf.2).resolve_left hf0
    obtain ⟨K, hK⟩ : J ∣ Ideal.span {f} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hfJ)
    have hKJ : K * J = Ideal.span {f} := by rw [hK, mul_comm]
    have hKne : K ≠ ⊥ := by
      rintro rfl
      rw [Ideal.bot_mul] at hKJ
      exact hf0 (Ideal.span_singleton_eq_bot.mp hKJ.symm)
    have hcod : codim W K ≤ m := by
      have := codim_mul W K J hKne hJ
      rw [hKJ, codim_span W hf0] at this
      omega
    have hcl : ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_of_ne_zero hKne⟩ = c := by
      have h1 : ClassGroup.mk0 ⟨K * J, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hKne hJ)⟩ = 1 :=
        (ClassGroup.mk0_eq_one_iff _).mpr (by rw [hKJ]; exact ⟨⟨f, rfl⟩⟩)
      have h2 : ClassGroup.mk0 (⟨K, mem_nonZeroDivisors_of_ne_zero hKne⟩ * ⟨J, hJ'⟩) = 1 := h1
      rw [map_mul, hJc] at h2
      exact mul_inv_eq_one.mp h2
    let I' : T := ⟨K, hKne, hcod, hcl⟩
    have hspan : Ideal.span {g I'} = (Ideal.span {f} : Ideal W.toAffine.CoordinateRing) := by
      rw [← hgI I', ← hKJ]
    obtain ⟨u, hu, hfu⟩ := exists_const_mul_of_span_eq W hspan
    exact ⟨(I', ⟨u, hu⟩), Subtype.ext (Subtype.ext hfu.symm)⟩
  have := Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  rw [Nat.card_prod, natCard_zmod_ne_zero, hA] at this
  exact this

/-- The ideal class group of $R$ has $\#E(\mathbb F_p) = N_1$ elements. -/
theorem card_classGroup : Nat.card (ClassGroup W.toAffine.CoordinateRing) = numPoints W 1 := by
  classical
  rw [numPoints_one]
  let e : W.toAffine.Point ≃ ClassGroup W.toAffine.CoordinateRing :=
    (WeierstrassCurve.Affine.Point.toClassEquiv (W := W.toAffine)).toEquiv.trans Additive.toMul
  exact (Nat.card_congr e).symm

/-- **Proposition 9.9** (pdf p. 162): the named statement `Prop9_9` holds for every elliptic curve over
$\mathbb F_p$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.9, pdf p. 162"]
theorem prop9_9 : Prop9_9 W := by
  classical
  refine ⟨fun m hm => ?_⟩
  have hfinP : Finite W.toAffine.Point := by
    refine Finite.of_injective (fun P : W.toAffine.Point => match P with
      | .zero => (none : Option (ZMod p × ZMod p))
      | .some (x := x) (y := y) _ => some (x, y)) ?_
    intro P Q h
    cases P <;> cases Q <;> simp at h ⊢
    exact h
  let e : W.toAffine.Point ≃ ClassGroup W.toAffine.CoordinateRing :=
    (WeierstrassCurve.Affine.Point.toClassEquiv (W := W.toAffine)).toEquiv.trans Additive.toMul
  haveI : Finite (ClassGroup W.toAffine.CoordinateRing) := Finite.of_equiv _ e
  haveI : Fintype (ClassGroup W.toAffine.CoordinateRing) := Fintype.ofFinite _
  let X := {I : Ideal W.toAffine.CoordinateRing // I ≠ ⊥ ∧ codim W I ≤ m}
  let f : X → ClassGroup W.toAffine.CoordinateRing := fun x =>
    ClassGroup.mk0 ⟨x.1, mem_nonZeroDivisors_of_ne_zero x.2.1⟩
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpm : 2 ≤ p ^ m := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
  have hfib : ∀ c, Nat.card {x : X // f x = c} * (p - 1) = p ^ m - 1 := by
    intro c
    have e2 : {x : X // f x = c} ≃ {I : Ideal W.toAffine.CoordinateRing // ∃ hI : I ≠ ⊥, codim W I ≤ m ∧
        ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = c} :=
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.choose, y.2.choose_spec.1⟩, y.2.choose_spec.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr e2]
    exact card_ideals_in_class W c m hm
  have hfin : ∀ c, Finite {x : X // f x = c} := fun c => by
    refine Nat.finite_of_card_ne_zero (fun h0 => ?_)
    have := hfib c
    rw [h0, zero_mul] at this
    omega
  have hcard : Nat.card X = ∑ c, Nat.card {x : X // f x = c} := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  rw [posDivCount_eq_card_ideals, show Nat.card {I : Ideal W.toAffine.CoordinateRing // I ≠ ⊥ ∧ codim W I ≤ m}
    = Nat.card X from rfl, hcard, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_classGroup, smul_eq_mul]

/-- **Theorem 9.10** (pdf p. 163), unconditional, by Milne's proof: for an elliptic curve over $\mathbb F_p$,
$Z(E, T) = \dfrac{1 + (N_1 - p - 1)T + pT^2}{(1 - T)(1 - pT)}$. -/
@[kb "milne2006ec" "Ch. IV, Theorem 9.10, pdf p. 163"]
theorem theorem_9_10_unconditional : Theorem9_10 W :=
  theorem_9_10_of_prop9_9 W (prop9_9 W)

/-- **Remark 9.11(a)** (pdf p. 164), unconditional: $N_m = 1 + p^m - \alpha^m - \beta^m$ for $m \ge 1$, where
$1 + (N_1 - p - 1)T + pT^2 = (1 - \alpha T)(1 - \beta T)$. -/
@[kb "milne2006ec" "Ch. IV, Remark 9.11(a), pdf p. 164"]
theorem remark_9_11_a_unconditional (α β : ℂ) (hsum : α + β = p + 1 - numPoints W 1) (hprod : α * β = p)
    (m : ℕ) (hm : 1 ≤ m) : (numPoints W m : ℂ) = 1 + (p : ℂ) ^ m - α ^ m - β ^ m :=
  remark_9_11_a W (theorem_9_10_unconditional W) α β hsum hprod m hm

end NumberFieldKB.MilneEC
