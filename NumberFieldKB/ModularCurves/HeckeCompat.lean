import NumberFieldKB.ModularCurves.HeckePic
import NumberFieldKB.ModularCurves.HeckeDivisors

/-!
# $T(p)$ on divisors of $X_0(N)$ restricts to $T(p)$ on divisors of $Y_0(N)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §7. The closed points of $Y_0(N)$ are among the places of
$\mathbb Q(X_0(N))$ (`Y0Point.toPlace`), so divisors of $Y_0(N)$ map into divisors of $X_0(N)$ by
`Finsupp.mapDomain Y0Point.toPlace`. We prove that this inclusion commutes with push-forward along $z \mapsto dz$
(`pushX0_mapDomain`), with pullback along $z \mapsto z$ (`pullX0_mapDomain`), hence with the Hecke correspondence
(`heckeX0_mapDomain`): $T(p)$ on divisors of $X_0(N)$ restricts to $T(p)$ on divisors of $Y_0(N)$.
-/

open Polynomial IsDedekindDomain

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The map $z \mapsto dz$ on places sends the place of a point of $Y_0(M)$ to the place of its image point. -/
theorem degeneracyPlace_toPlace {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) :
    degeneracyPlace h Q.toPlace = (degeneracyPoint h Q).toPlace := by
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  have hR : ∀ r : Y0Ring N, algebraMap (X0 N) (X0 M) (algebraMap (Y0Ring N) (X0 N) r) =
      algebraMap (Y0Ring M) (X0 M) (degeneracyY0 N M d h r) := fun r =>
    (degeneracyY0_coe h r).symm
  have hall : ∀ r : Y0Ring N, algebraMap (Y0Ring N) (X0 N) r ∈ (Q.toPlace.comap (K := X0 N)).O := by
    intro r
    rw [PrimeDivisor.mem_comap_O, hR]
    exact algebraMap_mem_valuationSubringAtPrime Q _
  obtain ⟨P', hP'⟩ := (exists_toPrimeDivisor_iff (R := Y0Ring N) (K := X0 N) exists_Y0_eq_algebraMap _).2 hall
  have hP'' : Y0Point.toPlace P' = Q.toPlace.comap (K := X0 N) := hP'
  have hPP : P' = degeneracyPoint h Q := by
    apply HeightOneSpectrum.ext
    ext r
    have h1 : r ∈ P'.asIdeal ↔ r = 0 ∨ (algebraMap (Y0Ring N) (X0 N) r)⁻¹ ∉ (Y0Point.toPlace P').O :=
      mem_asIdeal_iff_inv_not_mem (K := X0 N) P' r
    have h2 : degeneracyY0 N M d h r ∈ Q.asIdeal ↔ degeneracyY0 N M d h r = 0 ∨
        (algebraMap (Y0Ring M) (X0 M) (degeneracyY0 N M d h r))⁻¹ ∉ Q.toPlace.O :=
      mem_asIdeal_iff_inv_not_mem (K := X0 M) Q _
    have h3 : r ∈ (degeneracyPoint h Q).asIdeal ↔ degeneracyY0 N M d h r ∈ Q.asIdeal :=
      Ideal.mem_comap
    rw [h3, h1, h2, hP'', PrimeDivisor.mem_comap_O, map_inv₀, hR]
    constructor
    · rintro (h0 | h0)
      · exact Or.inl (by rw [h0, map_zero])
      · exact Or.inr h0
    · rintro (h0 | h0)
      · exact Or.inl (degeneracyY0_injective h (by rw [h0, map_zero]))
      · exact Or.inr h0
  rw [← hPP]
  exact hP''.symm

/-- Residue degrees of places agree with residue degrees of closed points. -/
theorem residueDeg_toPlace {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) :
    letI := (degeneracy N M d h).toAlgebra
    haveI := isScalarTower_rat_degeneracy h
    haveI := isAlgebraic_degeneracy h
    Q.toPlace.residueDeg (K := X0 N) = residueDeg h Q := by
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  have hc : Q.toPlace.comap (K := X0 N) = (degeneracyPoint h Q).toPlace := degeneracyPlace_toPlace h Q
  have hR : ∀ r : Y0Ring N, algebraMap (X0 N) (X0 M) (algebraMap (Y0Ring N) (X0 N) r) =
      algebraMap (Y0Ring M) (X0 M) (degeneracyY0 N M d h r) := fun r =>
    (degeneracyY0_coe h r).symm
  set P : Y0Point N := degeneracyPoint h Q with hPdef
  have hmem : ∀ x : (Y0Point.toPlace P).O, algebraMap (X0 N) (X0 M) x.1 ∈ Q.toPlace.O := by
    intro x
    have : x.1 ∈ (Q.toPlace.comap (K := X0 N)).O := by rw [hc]; exact x.2
    exact (PrimeDivisor.mem_comap_O _ _).1 this
  let ψ : (Y0Point.toPlace P).O →+* Q.toPlace.O :=
    ((algebraMap (X0 N) (X0 M)).comp (Y0Point.toPlace P).O.subtype).codRestrict Q.toPlace.O.toSubring hmem
  have hψ : ∀ x : (Y0Point.toPlace P).O, (ψ x : X0 M) = algebraMap (X0 N) (X0 M) x := fun x => rfl
  obtain ⟨_, hres⟩ := Q.toPlace.residueDeg_eq_of_comap_eq (Y0Point.toPlace P) hc ψ hψ
  refine hres.trans ?_
  letI := (degeneracyY0 N M d h).toAlgebra
  haveI : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  have : P.asIdeal.IsMaximal := P.isMaximal
  have : Q.asIdeal.IsMaximal := Q.isMaximal
  unfold residueDeg
  rw [Ideal.inertiaDeg_eq_of_isMaximal P.asIdeal]
  letI := (IsLocalRing.ResidueField.map ψ).toAlgebra
  let i : (Y0Ring N ⧸ P.asIdeal) ≃+* IsLocalRing.ResidueField (Y0Point.toPlace P).O :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
      (HeightOneSpectrum.valuationSubringAtPrime (X0 N) P)).toRingEquiv
  let j : (Y0Ring M ⧸ Q.asIdeal) ≃+* IsLocalRing.ResidueField Q.toPlace.O :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q.asIdeal
      (HeightOneSpectrum.valuationSubringAtPrime (X0 M) Q)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.ResidueField.map ψ (IsLocalRing.residue (Y0Point.toPlace P).O
      (algebraMap (Y0Ring N) (HeightOneSpectrum.valuationSubringAtPrime (X0 N) P) a)) =
    IsLocalRing.residue Q.toPlace.O
      (algebraMap (Y0Ring M) (HeightOneSpectrum.valuationSubringAtPrime (X0 M) Q) (degeneracyY0 N M d h a))
  refine (IsLocalRing.ResidueField.map_residue ψ _).trans ?_
  congr 1

/-- The place of a closed point, with the default `ℚ`-algebra instance on the function field. -/
noncomputable def placeOfY0 (Q : Y0Point M) : PrimeDivisor ℚ (X0 M) := Q.toPlace

variable (M) in
/-- The inclusion of divisors of $Y_0(M)$ into divisors of $X_0(M)$, as an additive homomorphism. -/
noncomputable def inclY0 : Y0Div M →+ Divisor ℚ (X0 M) :=
  Finsupp.mapDomain.addMonoidHom Y0Point.toPlace

theorem inclY0_single (Q : Y0Point M) (n : ℤ) :
    inclY0 M (Finsupp.single Q n) = Finsupp.single (placeOfY0 Q) n :=
  Finsupp.mapDomain_single

theorem degeneracyPlace_placeOf {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) :
    degeneracyPlace h (placeOfY0 Q) = placeOfY0 (degeneracyPoint h Q) :=
  degeneracyPlace_toPlace h Q

/-- Push-forward of a single place of $X_0(M)$. -/
theorem pushX0_single_compat {d : ℕ} (h : d * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) (n : ℤ) :
    letI := (degeneracy N M d h).toAlgebra
    haveI := isScalarTower_rat_degeneracy h
    haveI := isAlgebraic_degeneracy h
    pushX0 h (Finsupp.single Q n) =
      Finsupp.single (degeneracyPlace h Q) (n * (Q.residueDeg (K := X0 N) : ℤ)) := by
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  simp [pushX0, pushDiv, degeneracyPlace, Finsupp.smul_single]

/-- Push-forward commutes with the inclusion of divisors of Y_0 into divisors of X_0. -/
theorem pushX0_mapDomain {d : ℕ} (h : d * N ∣ M) (D : Y0Div M) :
    pushX0 h (D.mapDomain Y0Point.toPlace) = (pushY0 h D).mapDomain Y0Point.toPlace := by
  change pushX0 h (inclY0 M D) = inclY0 N (pushY0 h D)
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add, map_add]
  | single Q n =>
    rw [inclY0_single, pushX0_single_compat, pushY0_single, inclY0_single, degeneracyPlace_placeOf]
    have := residueDeg_toPlace h Q
    congr 2
    exact_mod_cast this

/-- The coefficient of the pullback of a divisor of $Y_0(N)$ at a closed point $Q$ of $Y_0(M)$. -/
theorem pullY0_apply (h : 1 * N ∣ M) (D : Y0Div N) (Q : Y0Point M) :
    letI := forgetY0Algebra N M h
    pullY0 h D Q = D (degeneracyPoint h Q) * (Q.asIdeal.ramificationIdx (Y0Ring N) : ℤ) := by
  letI := forgetY0Algebra N M h
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, Finsupp.add_apply, hD, hE, Finsupp.add_apply, add_mul]
  | single P n =>
    letI := fintypePrimesOverY0 h P
    simp only [pullY0, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, smul_eq_mul]
    by_cases hQ : degeneracyPoint h Q = P
    · subst hQ
      have hmem : Q.asIdeal ∈ (degeneracyPoint h Q).asIdeal.primesOver (Y0Ring M) :=
        ⟨Q.isPrime, ⟨rfl⟩⟩
      rw [Finset.sum_eq_single (⟨Q.asIdeal, hmem⟩ : (degeneracyPoint h Q).asIdeal.primesOver (Y0Ring M))]
      · simp [primesOverToPoint]
      · intro q _ hne
        have : primesOverToPoint h (degeneracyPoint h Q) q ≠ Q := fun e =>
          hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal e))
        simp [Finsupp.single_apply, this]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [Finset.sum_eq_zero]
      · simp [Finsupp.single_apply, Ne.symm hQ]
      · intro q _
        have : primesOverToPoint h P q ≠ Q := fun e => hQ (by rw [← e, degeneracyPoint_primesOverToPoint])
        simp [Finsupp.single_apply, this]

theorem inclY0_apply_placeOf (D : Y0Div M) (Q : Y0Point M) : inclY0 M D (placeOfY0 Q) = D Q :=
  Finsupp.mapDomain_apply_of_injective Y0Point.toPlace_injective D Q

theorem inclY0_apply_cusp (D : Y0Div M) (Q : PrimeDivisor ℚ (X0 M)) (hQ : IsCusp Q) :
    inclY0 M D Q = 0 := by
  refine Finsupp.mapDomain_of_notMem_range D Q ?_
  rintro ⟨Q', hQ'⟩
  exact hQ ((exists_toPlace_iff Q).1 ⟨Q', hQ'⟩)

/-- Pullback commutes with the inclusion of divisors of Y_0 into divisors of X_0. -/
theorem pullX0_mapDomain (h : 1 * N ∣ M) (D : Y0Div N) :
    pullX0 h (D.mapDomain Y0Point.toPlace) = (pullY0 h D).mapDomain Y0Point.toPlace := by
  change pullX0 h (inclY0 N D) = inclY0 M (pullY0 h D)
  ext Q
  rw [pullX0_apply]
  by_cases hj : jX0 (prop2_4' M) ∈ Q.O
  · obtain ⟨Q', rfl⟩ := (exists_toPlace_iff Q).2 hj
    change inclY0 N D (degeneracyPlace h (placeOfY0 Q')) * _ = inclY0 M (pullY0 h D) (placeOfY0 Q')
    have e := degeneracyPlace_toPlace h Q'
    have hr := ramIndex_toPlace h _ Q' rfl
    rw [degeneracyPlace_placeOf, inclY0_apply_placeOf, inclY0_apply_placeOf, pullY0_apply]
    rw [e, hr]
  · have hc : IsCusp Q := hj
    rw [inclY0_apply_cusp _ Q hc]
    have : IsCusp (degeneracyPlace h Q) := by
      letI := forgetAlgebra N M h
      haveI := isScalarTower_rat_forget (N := N) (M := M) h
      haveI := isAlgebraic_forget (N := N) (M := M) h
      exact (isCusp_comap_forget_iff h Q).2 hc
    rw [inclY0_apply_cusp _ _ this, zero_mul]

/-- **T(p) on X_0(N) restricts to T(p) on Y_0(N)**. -/
theorem heckeX0_mapDomain (N p : ℕ) [NeZero N] [NeZero p] (D : Y0Div N) :
    heckeX0 N p (D.mapDomain Y0Point.toPlace) = (heckeDiv N p D).mapDomain Y0Point.toPlace := by
  change heckeX0 N p (inclY0 N D) = inclY0 N (heckeDiv N p D)
  have h1 : pullX0 (d := 1) (one_mul_dvd_mul N p) (inclY0 N D) =
      inclY0 (p * N) (pullY0 (one_mul_dvd_mul N p) D) := pullX0_mapDomain _ D
  have h2 := pushX0_mapDomain (d := p) (dvd_rfl : p * N ∣ p * N) (pullY0 (one_mul_dvd_mul N p) D)
  rw [heckeX0, heckeDiv, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, h1]
  exact h2

end NumberFieldKB.ModularCurves
