import NumberFieldKB.ModularCurves.Places

/-!
# The image of a place under a finite morphism of curves

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 (prime divisors, pdf p. 45) and Ch. V, §7 (correspondences).
A nonconstant morphism of curves $C \to C'$ corresponds to a finite extension $k(C) \subseteq k(C')$ of function
fields; the image of a point $Q$ of $C$ is the place of $k(C')$ obtained by restricting $Q$:
$\mathcal O_{\pi Q} = \mathcal O_Q \cap k(C')$. Here, for an algebraic extension $L/K$ and a place `Q` of `L`
(Milne's `MilneEC.PrimeDivisor`), `PrimeDivisor.comap Q` is that place of `K`. Its valuation ring is a discrete
valuation ring because the restricted valuation has a nontrivial subgroup of $\mathbb Z$ as value group (Mathlib's
`Valuation.valuationSubring_isDiscreteValuationRing`).
-/

open IsDedekindDomain

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC
open scoped WithZero

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

/-- The normalized valuation of a place, $\mathbb Z$-valued (`ℤᵐ⁰`). -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.valuation (Q : PrimeDivisor k L) : Valuation L ℤᵐ⁰ :=
  haveI := Q.isDVR
  (IsDiscreteValuationRing.maximalIdeal Q.O).valuation L

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.mem_O_iff_valuation_le_one (Q : PrimeDivisor k L) (x : L) :
    x ∈ Q.O ↔ Q.valuation x ≤ 1 := by
  haveI := Q.isDVR
  have h := IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := Q.O) (K := L)
  constructor
  · intro hx
    have : x ∈ Subring.map (algebraMap Q.O L) ⊤ := ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [h] at this
    exact this
  · intro hx
    have : x ∈ ((IsDiscreteValuationRing.maximalIdeal Q.O).valuation L).valuationSubring.toSubring := hx
    rw [← h] at this
    obtain ⟨y, _, rfl⟩ := this
    exact y.2

variable [Algebra.IsAlgebraic K L]

omit [Algebra k K] [IsScalarTower k K L] in
/-- The valuation ring of a place of `L` does not contain all of `K` (`L/K` algebraic). -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.exists_not_mem_comap (Q : PrimeDivisor k L) :
    ∃ x : K, algebraMap K L x ∉ Q.O := by
  by_contra! h
  apply PrimeDivisor.O_ne_top Q
  rw [eq_top_iff]
  intro y _
  -- `y` is integral over `Q.O`, since it is algebraic over `K` and `K` lies in `Q.O`
  obtain ⟨f, hfm, hf⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  let φ : K →+* Q.O := (algebraMap K L).codRestrict Q.O.toSubring h
  have hc : (algebraMap Q.O L).comp φ = algebraMap K L := rfl
  have hint : IsIntegral Q.O y := ⟨f.map φ, hfm.map φ, by rw [Polynomial.eval₂_map, hc]; exact hf⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.O) (K := L)).1 hint
  rw [← hz]
  exact z.2

/-- **The image of a place** under the morphism of curves given by $K \subseteq L$: the place of `K` with valuation
ring $\mathcal O_Q \cap K$. -/
@[kb "milne2006ec" "Ch. I, §4, prime divisors; the image of a point under a nonconstant map of curves, pdf p. 45"]
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.comap (Q : PrimeDivisor k L) : PrimeDivisor k K where
  O := (Q.valuation.comap (algebraMap K L)).valuationSubring
  algebraMap_mem c := by
    change Q.valuation (algebraMap K L (algebraMap k K c)) ≤ 1
    rw [← IsScalarTower.algebraMap_apply, ← PrimeDivisor.mem_O_iff_valuation_le_one]
    exact Q.algebraMap_mem c
  isDVR := by
    set v := Q.valuation.comap (algebraMap K L)
    haveI : IsCyclic v.valueGroup := inferInstance
    haveI : Nontrivial v.valueGroup := by
      obtain ⟨x, hx⟩ := Q.exists_not_mem_comap (K := K)
      rw [PrimeDivisor.mem_O_iff_valuation_le_one, not_le] at hx
      have hx0 : v x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
      rw [Subgroup.nontrivial_iff_exists_ne_one]
      refine ⟨Units.mk0 (v x) hx0, MonoidWithZeroHom.mem_valueGroup _ ⟨x, rfl⟩, fun h => ?_⟩
      have := congrArg Units.val h
      simp only [Units.val_mk0, Units.val_one] at this
      exact absurd this (ne_of_gt hx)
    exact Valuation.valuationSubring_isDiscreteValuationRing v

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.mem_comap_O (Q : PrimeDivisor k L) (x : K) :
    x ∈ (Q.comap (K := K)).O ↔ algebraMap K L x ∈ Q.O := by
  change Q.valuation (algebraMap K L x) ≤ 1 ↔ _
  rw [Q.mem_O_iff_valuation_le_one]

/-! ### Residue degrees and push-forward of divisors -/

/-- The inclusion $\mathcal O_{\pi Q} \to \mathcal O_Q$. -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.comapHom (Q : PrimeDivisor k L) :
    (Q.comap (K := K)).O →+* Q.O :=
  ((algebraMap K L).comp (Q.comap (K := K)).O.subtype).codRestrict Q.O.toSubring
    fun x => (Q.mem_comap_O x.1).1 x.2

instance (Q : PrimeDivisor k L) : IsLocalHom (Q.comapHom (K := K)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    have : ((Q.comapHom (K := K) x : Q.O) : L) = 0 := by
      change algebraMap K L x = 0
      rw [h0, map_zero]
    rw [← hu] at this
    exact u.ne_zero (Subtype.ext this)
  have hinv : (x : K)⁻¹ ∈ (Q.comap (K := K)).O := by
    rw [Q.mem_comap_O, map_inv₀]
    have e : algebraMap K L x = ((u : Q.O) : L) := by rw [hu]; rfl
    rw [e, ← PrimeDivisor.coe_unit_inv]
    exact ((u⁻¹ : Q.Oˣ) : Q.O).2
  exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : (Q.comap (K := K)).O) (Subtype.ext (by simp [hx0]))

/-- The residue field extension $\kappa(\pi Q) \to \kappa(Q)$. -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.residueMap (Q : PrimeDivisor k L) :
    IsLocalRing.ResidueField (Q.comap (K := K)).O →+* IsLocalRing.ResidueField Q.O :=
  IsLocalRing.ResidueField.map (Q.comapHom (K := K))

/-- The **residue degree** $f(Q / \pi Q) = [\kappa(Q) : \kappa(\pi Q)]$. -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.residueDeg (Q : PrimeDivisor k L) : ℕ :=
  letI := (Q.residueMap (K := K)).toAlgebra
  Module.finrank (IsLocalRing.ResidueField (Q.comap (K := K)).O) (IsLocalRing.ResidueField Q.O)

/-- **The degrees multiply**: $\deg Q = f(Q/\pi Q) \deg \pi Q$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.deg_eq_residueDeg_mul (Q : PrimeDivisor k L) :
    Q.deg = Q.residueDeg (K := K) * (Q.comap (K := K)).deg := by
  letI : Module k (IsLocalRing.ResidueField Q.O) := ((IsLocalRing.residue Q.O).comp Q.ofBase).toModule
  letI iP : Algebra k (IsLocalRing.ResidueField (Q.comap (K := K)).O) :=
    ((IsLocalRing.residue (Q.comap (K := K)).O).comp (Q.comap (K := K)).ofBase).toAlgebra
  letI iQ : Algebra k (IsLocalRing.ResidueField Q.O) := ((IsLocalRing.residue Q.O).comp Q.ofBase).toAlgebra
  letI := (Q.residueMap (K := K)).toAlgebra
  haveI : IsScalarTower k (IsLocalRing.ResidueField (Q.comap (K := K)).O) (IsLocalRing.ResidueField Q.O) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change IsLocalRing.residue Q.O (Q.ofBase c) =
      Q.residueMap (K := K) (IsLocalRing.residue _ ((Q.comap (K := K)).ofBase c))
    rw [PrimeDivisor.residueMap, IsLocalRing.ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change algebraMap k L c = algebraMap K L (algebraMap k K c)
    rw [IsScalarTower.algebraMap_apply k K L]
  have h := Module.finrank_mul_finrank k (IsLocalRing.ResidueField (Q.comap (K := K)).O)
    (IsLocalRing.ResidueField Q.O)
  unfold PrimeDivisor.deg PrimeDivisor.residueDeg
  rw [← h, mul_comm]

/-- **Push-forward of divisors** along the morphism given by $K \subseteq L$: $[Q] \mapsto f(Q/\pi Q)\,[\pi Q]$. -/
noncomputable def pushDiv : Divisor k L →+ Divisor k K :=
  Finsupp.liftAddHom fun Q => zmultiplesHom (Divisor k K)
    (Finsupp.single (Q.comap (K := K)) (Q.residueDeg (K := K) : ℤ))

/-- **Push-forward preserves degrees.** -/
theorem deg_pushDiv (D : Divisor k L) : Divisor.deg (pushDiv (K := K) D) = Divisor.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add]
  | single Q n =>
    simp only [pushDiv, Divisor.deg, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
      map_zsmul, smul_eq_mul]
    rw [Q.deg_eq_residueDeg_mul (K := K)]
    push_cast
    ring

/-! ### The forgetful map $X_0(M) \to X_0(N)$ on points -/

section Forget

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem isAlgebraic_forget (h : 1 * N ∣ M) :
    letI := forgetAlgebra N M h
    Algebra.IsAlgebraic (X0 N) (X0 M) := by
  letI := forgetAlgebra N M h
  haveI := finite_forget (N := N) (M := M) h
  exact Algebra.IsAlgebraic.of_finite _ _

/-- **$z \mapsto z$ on points of $Y_0$, as places**: the image of the place of a closed point $Q$ of $Y_0(M)$ is the
place of its image point in $Y_0(N)$. -/
theorem comap_toPlace_forget (h : 1 * N ∣ M) (Q : Y0Point M) :
    letI := forgetAlgebra N M h
    haveI := isScalarTower_rat_forget (N := N) (M := M) h
    haveI := isAlgebraic_forget (N := N) (M := M) h
    (Q.toPlace).comap (K := X0 N) = (degeneracyPoint h Q).toPlace := by
  letI := forgetAlgebra N M h
  haveI := isScalarTower_rat_forget (N := N) (M := M) h
  haveI := isAlgebraic_forget (N := N) (M := M) h
  -- the image place contains `j`, so it comes from a point `P'` of `Y_0(N)`
  have hι : ∀ x : X0 N, algebraMap (X0 N) (X0 M) x = degeneracy N M 1 h x := fun _ => rfl
  have hj : jX0 (prop2_4' N) ∈ ((Q.toPlace).comap (K := X0 N)).O := by
    rw [PrimeDivisor.mem_comap_O, hι, degeneracy_jX0, jNElt_one]
    exact (exists_toPlace_iff _).1 ⟨Q, rfl⟩
  obtain ⟨P', hP'⟩ := (exists_toPlace_iff _).2 hj
  rw [← hP']
  congr 1
  apply HeightOneSpectrum.ext
  ext r
  have hR : ∀ r : Y0Ring N, algebraMap (X0 N) (X0 M) (algebraMap (Y0Ring N) (X0 N) r) =
      algebraMap (Y0Ring M) (X0 M) (degeneracyY0 N M 1 h r) := fun r => by
    rw [hι]
    exact (degeneracyY0_coe h r).symm
  have h1 : r ∈ P'.asIdeal ↔ r = 0 ∨ (algebraMap (Y0Ring N) (X0 N) r)⁻¹ ∉ P'.toPlace.O :=
    mem_asIdeal_iff_inv_not_mem (K := X0 N) P' r
  have h2 : degeneracyY0 N M 1 h r ∈ Q.asIdeal ↔ degeneracyY0 N M 1 h r = 0 ∨
      (algebraMap (Y0Ring M) (X0 M) (degeneracyY0 N M 1 h r))⁻¹ ∉ Q.toPlace.O :=
    mem_asIdeal_iff_inv_not_mem (K := X0 M) Q _
  rw [h1, Ideal.mem_comap.symm.trans (Iff.rfl : _ ↔ r ∈ (degeneracyPoint h Q).asIdeal) |>.symm.trans h2, hP',
    PrimeDivisor.mem_comap_O, map_inv₀, hR]
  constructor
  · rintro (h0 | h0)
    · exact Or.inl (by rw [h0, map_zero])
    · exact Or.inr h0
  · rintro (h0 | h0)
    · exact Or.inl (degeneracyY0_injective h (by rw [h0, map_zero]))
    · exact Or.inr h0

/-- **$z \mapsto z$ maps cusps to cusps and points of $Y_0$ to points of $Y_0$**: a place of $\mathbb Q(X_0(M))$ is a
cusp iff its image in $X_0(N)$ is ($j$ pulls back to $j$). -/
theorem isCusp_comap_forget_iff (h : 1 * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) :
    letI := forgetAlgebra N M h
    haveI := isScalarTower_rat_forget (N := N) (M := M) h
    haveI := isAlgebraic_forget (N := N) (M := M) h
    IsCusp (Q.comap (K := X0 N)) ↔ IsCusp Q := by
  letI := forgetAlgebra N M h
  haveI := isScalarTower_rat_forget (N := N) (M := M) h
  haveI := isAlgebraic_forget (N := N) (M := M) h
  have hι : algebraMap (X0 N) (X0 M) (jX0 (prop2_4' N)) = jX0 (prop2_4' M) := by
    change degeneracy N M 1 h _ = _
    rw [degeneracy_jX0, jNElt_one]
  unfold IsCusp
  rw [PrimeDivisor.mem_comap_O, hι]

end Forget

/-! ### The degeneracy maps $X_0(M) \to X_0(N)$, $z \mapsto dz$, are finite -/

section Degeneracy

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- $j$ is integral over $\mathbb Q(X_0(N))$ embedded by $z \mapsto dz$ (a root of $F_d(j_d, Y)$). -/
theorem isIntegral_jX0_degeneracy {d : ℕ} (h : d * N ∣ M) :
    letI := (degeneracy N M d h).toAlgebra
    IsIntegral (X0 N) (jX0 (prop2_4' M)) := by
  letI := (degeneracy N M d h).toAlgebra
  obtain ⟨f, hfm, hf⟩ := isIntegralElem_jY0 (N := N) (M := M) h
  refine ⟨f.map (algebraMap (Y0Ring N) (X0 N)), hfm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (X0 N) (X0 M)).comp (algebraMap (Y0Ring N) (X0 N)) =
      (algebraMap (Y0Ring M) (X0 M)).comp (degeneracyY0 N M d h) := by
    ext r
    exact (degeneracyY0_coe h r).symm
  rw [hc, show jX0 (prop2_4' M) = algebraMap (Y0Ring M) (X0 M) (jY0 M) from rfl, ← Polynomial.hom_eval₂, hf,
    map_zero]

/-- **$\mathbb Q(X_0(M))$ is algebraic over $\mathbb Q(X_0(N))$ embedded by $z \mapsto dz$** ($dN \mid M$). -/
theorem isAlgebraic_degeneracy {d : ℕ} (h : d * N ∣ M) :
    letI := (degeneracy N M d h).toAlgebra
    Algebra.IsAlgebraic (X0 N) (X0 M) := by
  letI := (degeneracy N M d h).toAlgebra
  set S := Algebra.adjoin (X0 N) ({jX0 (prop2_4' M)} : Set (X0 M))
  haveI : Algebra.IsIntegral (X0 N) S := Algebra.IsIntegral.adjoin fun x hx => by
    rw [Set.mem_singleton_iff.1 hx]; exact isIntegral_jX0_degeneracy h
  haveI : Algebra.IsAlgebraic (X0 N) S := inferInstance
  refine ⟨fun y => ?_⟩
  -- `y` is algebraic over `ℚ[j] ⊆ S`
  let φ : Polynomial ℚ →+* S := Polynomial.eval₂RingHom ((algebraMap (X0 N) S).comp (algebraMap ℚ (X0 N)))
    ⟨jX0 (prop2_4' M), Algebra.subset_adjoin rfl⟩
  have hφ : (algebraMap S (X0 M)).comp φ = algebraMap (Polynomial ℚ) (X0 M) := by
    rw [algebraMap_polyX0_eq]
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat (((algebraMap S (X0 M)).comp φ).comp Polynomial.C)
        (((Polynomial.aeval (jX0 (prop2_4' M))).toRingHom).comp Polynomial.C)) a
    · simp [φ]
  have hy : IsAlgebraic (Polynomial ℚ) y := by
    have h1 : IsAlgebraic (RatFunc ℚ) y := Algebra.IsAlgebraic.isAlgebraic y
    haveI : Algebra.IsAlgebraic (Polynomial ℚ) (RatFunc ℚ) :=
      IsLocalization.isAlgebraic (S := RatFunc ℚ) (nonZeroDivisors (Polynomial ℚ))
    exact h1.restrictScalars (Polynomial ℚ)
  obtain ⟨f, hf0, hf⟩ := hy
  have hinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (algebraMap S (X0 M)) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hφ] at this
    have hinj0 : Function.Injective (algebraMap (Polynomial ℚ) (X0 M)) := by
      rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) (RatFunc ℚ) (X0 M), RingHom.coe_comp]
      exact (algebraMap (RatFunc ℚ) (X0 M)).injective.comp (IsFractionRing.injective _ _)
    exact hinj0 this
  have hyS : IsAlgebraic S y := by
    refine ⟨f.map φ, (Polynomial.map_ne_zero_iff hinj).2 hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hφ]
    exact hf
  exact hyS.restrictScalars (X0 N)

end Degeneracy

end NumberFieldKB.ModularCurves
