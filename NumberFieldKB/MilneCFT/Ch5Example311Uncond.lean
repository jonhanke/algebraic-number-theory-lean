import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Ch5ConductorUncond
import NumberFieldKB.TauCetiPort.NumberTheory.Multiquadratic.Cyclotomic.Conductor
import NumberFieldKB.TauCetiPort.NumberTheory.Multiquadratic.Quadratic.Discriminant

/-!
# Milne, *Class Field Theory*, Chapter V, Example 3.11 (the conductor of a quadratic field), unconditional

The named statement `Example3_11` is proved here (`example3_11`).  Let $L=\mathbb Q(s)$, $s^2=d$ with $d\ne1$
squarefree, and $D$ the fundamental discriminant of $d$ (Tau Ceti, `fundamentalDiscriminant`).

* `Ex311.discr_eq`: $\operatorname{disc}(L)=D$ (Tau Ceti's `discr_adjoin_singleton_eq_fundamentalDiscriminant`
  transported to $L$ along $\mathbb Q(s)\simeq L$).
* `mem_cyclotomic`: $L\to\mathbb Q(\zeta_n)$ exists iff a square root of $d$ lies in $\mathbb Q(\zeta_n)$ (the image of
  $s$ for one direction, and for the other a square root in $\mathbb C$ together with
  $\mathbb Q(\zeta)\simeq\mathbb Q(\zeta_n)$), iff $|D|\mid n$ (Tau Ceti's
  `mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd`).
* `conductor`: for the conductor $\mathfrak f$ of $L$ (`exists_artinConductor`) we show $\mathfrak f\mid(|D|,\infty^\epsilon)$
  and the converse.  The finite part: $L\subseteq\mathbb Q(\zeta_{|D|})$, the ray class field of $\infty(|D|)$
  (`example_3_10_cyclotomic`), so $\mathfrak f\mid\infty(|D|)$ by `remark_3_8_subfield`; writing the finite part of
  $\mathfrak f$ as $(c)$, $\mathfrak f\mid\infty(c)$ gives $L\subseteq\mathbb Q(\zeta_c)$, so $|D|\mid c$ by
  `mem_cyclotomic`.  The infinite part: a place of $L$ is complex iff $d<0$ (for an embedding $\varphi$,
  $\varphi(s)^2=d$), so by `artinConductor_support` the real place lies in $\mathfrak f$ iff $d<0$.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

namespace Ex311

variable {L : Type} [Field L] [NumberField L] {d : ℤ} {s : L}

theorem not_isSquare (hd : Squarefree d) (hd1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro h
  rw [Rat.isSquare_intCast_iff] at h
  obtain ⟨r, hr⟩ := h
  have hu : IsUnit r := hd r ⟨1, by rw [hr]; ring⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> simp [hr, h1] at hd1

omit [NumberField L] in
theorem sq_eq_algebraMap (hs : s ^ 2 = d) : s ^ 2 = algebraMap ℤ L d := by
  simpa using hs

theorem adjoin_eq_top (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) : IntermediateField.adjoin ℚ {s} = ⊤ := by
  have h2 : Module.finrank ℚ (IntermediateField.adjoin ℚ {s}) = 2 :=
    TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
      (a := ((d : ℤ) : ℚ)) (by simpa using hs) (not_isSquare hd hd1)
  exact IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h2, IntermediateField.finrank_top', hfin])

theorem algebra_adjoin_eq_top (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) : Algebra.adjoin ℚ {s} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic s), adjoin_eq_top hd hd1 hs hfin, IntermediateField.top_toSubalgebra]

theorem discr_eq (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (hfin : Module.finrank ℚ L = 2) :
    discr L = TauCeti.Multiquadratic.fundamentalDiscriminant d := by
  have hE := adjoin_eq_top hd hd1 hs hfin
  have h := TauCeti.Multiquadratic.discr_adjoin_singleton_eq_fundamentalDiscriminant hd
    (sq_eq_algebraMap hs) (not_isSquare hd hd1)
  dsimp only at h
  let e : IntermediateField.adjoin ℚ {s} ≃ₐ[ℚ] L :=
    (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
  exact (NumberField.discr_eq_discr_of_algEquiv _ e).symm.trans h

theorem fundDisc_natAbs_pos (hd : Squarefree d) :
    0 < (TauCeti.Multiquadratic.fundamentalDiscriminant d).natAbs :=
  Int.natAbs_pos.mpr (TauCeti.Multiquadratic.isFundamentalDiscr_fundamentalDiscriminant hd).ne_zero

/-- A homomorphism into a cyclotomic field forces the divisibility. -/
theorem dvd_of_algHom (hd : Squarefree d) (hs : s ^ 2 = d) {n : ℕ} (hn : 0 < n)
    (f : L →ₐ[ℚ] CyclotomicField n ℚ) :
    (TauCeti.Multiquadratic.fundamentalDiscriminant d).natAbs ∣ n := by
  have : NeZero n := ⟨hn.ne'⟩
  have := CyclotomicField.isCyclotomicExtension n ℚ
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have htop : IntermediateField.adjoin ℚ {IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top.isAlgebraic), IntermediateField.top_toSubalgebra]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  refine (TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hn hζ hd
    (x := f s) ?_).mp (by rw [htop]; exact IntermediateField.mem_top)
  rw [← map_pow, hs]; simp

/-- Conversely, if `|D| ∣ n` then `L` embeds in `ℚ(ζ_n)`. -/
theorem nonempty_algHom (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) {n : ℕ} (hn : 0 < n)
    (hdvd : (TauCeti.Multiquadratic.fundamentalDiscriminant d).natAbs ∣ n) :
    Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  have : NeZero n := ⟨hn.ne'⟩
  have := CyclotomicField.isCyclotomicExtension n ℚ
  have hgen := algebra_adjoin_eq_top hd hd1 hs hfin
  let A := AlgebraicClosure ℚ
  let φ : L →ₐ[ℚ] A := IsAlgClosed.lift
  let ι : CyclotomicField n ℚ →ₐ[ℚ] A := IsAlgClosed.lift
  have hζ0 := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hζ : IsPrimitiveRoot (ι (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) n :=
    hζ0.map_of_injective ι.injective
  have hmem : φ s ∈ IntermediateField.adjoin ℚ {ι (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))} :=
    (TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hn hζ hd
      (x := φ s) (by rw [← map_pow, hs]; simp)).mpr hdvd
  have hrange : φ s ∈ ι.range := by
    have hle : IntermediateField.adjoin ℚ {ι (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))} ≤
        ι.fieldRange :=
      IntermediateField.adjoin_le_iff.mpr (by simp)
    exact hle hmem
  have hle : (Algebra.adjoin ℚ {s}).map φ ≤ ι.range := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    exact Algebra.adjoin_le (by simpa using hrange)
  have hall : ∀ y : L, φ y ∈ ι.range := fun y =>
    hle (Subalgebra.mem_map.mpr ⟨y, by rw [hgen]; trivial, rfl⟩)
  exact ⟨((AlgEquiv.ofInjective ι ι.injective).symm : ι.range →ₐ[ℚ] _).comp (φ.codRestrict ι.range hall)⟩


theorem mem_cyclotomic_aux (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) :
    Nonempty (L →ₐ[ℚ] CyclotomicField (discr L).natAbs ℚ) ∧
        ∀ n : ℕ, 0 < n → Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) → (discr L).natAbs ∣ n := by
  rw [discr_eq hd hd1 hs hfin]
  exact ⟨nonempty_algHom hd hd1 hs hfin (fundDisc_natAbs_pos hd) dvd_rfl,
    fun n hn ⟨f⟩ => dvd_of_algHom hd hs hn f⟩

/-! ## The infinite place -/

/-- An embedding of `L = ℚ(√d)` into `ℂ` is real iff `d > 0`. -/
theorem isReal_embedding_iff (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) (φ : L →+* ℂ) :
    ComplexEmbedding.IsReal φ ↔ 0 < d := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hz : (φ s) ^ 2 = (d : ℂ) := by rw [← map_pow, hs]; simp
  rw [ComplexEmbedding.isReal_iff]
  constructor
  · intro h
    have hc : (starRingEnd ℂ) (φ s) = φ s := by
      rw [← ComplexEmbedding.conjugate_coe_eq, h]
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc
    rw [hr] at hz
    have h2 : r ^ 2 = (d : ℝ) := by exact_mod_cast hz
    have : (0 : ℝ) < d := lt_of_le_of_ne (h2 ▸ sq_nonneg r) (by exact_mod_cast hd0.symm)
    exact_mod_cast this
  · intro hpos
    have hr : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hpos.le)]; simp
    have hc : (starRingEnd ℂ) (φ s) = φ s := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans hr.symm) with h | h <;> rw [h] <;> simp
    have hgen := algebra_adjoin_eq_top hd hd1 hs hfin
    have key : (ComplexEmbedding.conjugate φ).toRatAlgHom = φ.toRatAlgHom :=
      AlgHom.ext_of_adjoin_eq_top hgen (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simpa using hc)
    exact RingHom.ext fun x => by simpa using congrArg (fun g => g x) key

/-- A place of `L = ℚ(√d)` is complex iff `d < 0`. -/
theorem isComplex_iff (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) (u : InfinitePlace L) : u.IsComplex ↔ d < 0 := by
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
    isReal_embedding_iff hd hd1 hs hfin, not_lt]
  constructor
  · intro h; exact lt_of_le_of_ne h hd.ne_zero
  · intro h; exact h.le

/-- The real place of `ℚ` ramifies in `L = ℚ(√d)` iff `d < 0`. -/
theorem ramifiesIn_iff (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hfin : Module.finrank ℚ L = 2) (w : InfinitePlace ℚ) : InfinitePlace.RamifiesIn L w ↔ d < 0 := by
  constructor
  · rintro ⟨-, u, -, hu⟩
    exact (isComplex_iff hd hd1 hs hfin u).mp hu
  · intro hneg
    let φ : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
    refine ⟨by rw [Subsingleton.elim w Rat.infinitePlace]; exact Rat.isReal_infinitePlace,
      InfinitePlace.mk φ.toRingHom, Subsingleton.elim _ _, ?_⟩
    exact (isComplex_iff hd hd1 hs hfin _).mpr hneg

/-! ## Cyclotomic fields as class fields -/

open scoped IsMulCommutative in
/-- `ℚ(ζ_m)` is the ray class field of `ℚ` for `∞(m)` (the proof of `example_3_10_cyclotomic`, which does not use
its hypothesis `m % 4 ≠ 2`). -/
theorem cyclotomic_isClassField (m : ℕ) (hm : m ≠ 0) (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L] :
    IsClassFieldOf L (ratModulus m hm) (rayPrincipal (ratModulus m hm)) := by
  have : NeZero m := ⟨hm⟩
  have hirr := Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm)
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
  have hinj : Function.Injective (hζ.autToPow ℚ) := fun g h hgh =>
    (IsCyclotomicExtension.autEquivPow L hirr).injective hgh
  refine ⟨⟨fun v hv => unramifiedPrimes_cyclotomic_of_not_dvd m L v ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · intro hdvd
    apply hv
    rw [ratModulus_finiteSupport m hm]
    exact hdvd
  · exfalso
    apply hw
    show w.IsReal
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  · intro σ
    obtain ⟨a, ha⟩ := Psi_surj m hm (hζ.autToPow ℚ σ)
    refine ⟨⟨toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ), a.2⟩, hinj ?_⟩
    rw [autToPow_artinMap_rat m hm L a _ rfl, ha]
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨c, hc⟩ := T_surj (x : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ)
    have hcG : c ∈ Gm m hm := by
      show toPrincipalIdeal (𝓞 ℚ) ℚ c ∈ coprimeIdeals (ratModulus m hm)
      rw [hc]; exact x.2
    have key := autToPow_artinMap_rat m hm L ⟨c, hcG⟩ x hc.symm
    have h1 : artinMap L (ratModulus m hm).finiteSupport x = 1 ↔ Psi m hm ⟨c, hcG⟩ = 1 := by
      rw [← key, ← map_one (hζ.autToPow ℚ)]
      exact hinj.eq_iff.symm
    rw [h1, ← Theta_iff_Psi, Theta_eq_one_iff]
    constructor
    · rintro ⟨d, hd, hdc⟩
      exact ⟨d, hd, by rw [hdc, hc]⟩
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hd, by rw [hdx, hc]⟩

theorem modulus_dvd_trans {f g m : Modulus ℚ} (h1 : f.Dvd g) (h2 : g.Dvd m) : f.Dvd m :=
  ⟨dvd_trans h1.1 h2.1, h1.2.trans h2.2⟩

/-- The conductor of `ℚ(√d)` (Milne V, Example 3.11). -/
theorem conductor_aux (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (d : ℤ) (s : L)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (hfin : Module.finrank ℚ L = 2)
    (hn : (discr L).natAbs ≠ 0) :
    IsArtinConductor L (ratModulusOf (discr L).natAbs hn (decide (d < 0))) := by
  obtain ⟨hexist, hmin⟩ := mem_cyclotomic_aux hd hd1 hs hfin
  obtain ⟨f, hf⟩ := exists_artinConductor (K := ℚ) L
  obtain ⟨-, hsup⟩ := artinConductor_support L hf
  have hinf : ∀ w, w ∈ f.infinite ↔ d < 0 := fun w => (hsup w).trans (ramifiesIn_iff hd hd1 hs hfin w)
  -- `f ∣ F`
  have : NeZero (discr L).natAbs := ⟨hn⟩
  have := CyclotomicField.isCyclotomicExtension (discr L).natAbs ℚ
  have := IsCyclotomicExtension.isAbelianGalois {(discr L).natAbs} ℚ (CyclotomicField (discr L).natAbs ℚ)
  have hclass := cyclotomic_isClassField (discr L).natAbs hn (CyclotomicField (discr L).natAbs ℚ)
  have hfd : f.Dvd (ratModulus (discr L).natAbs hn) :=
    (remark_3_8_subfield L _ _ hclass f hf).mp hexist
  have hfF : f.Dvd (ratModulusOf (discr L).natAbs hn (decide (d < 0))) := by
    refine ⟨hfd.1, fun w hw => ?_⟩
    by_cases hneg : d < 0
    · simpa [ratModulusOf, hneg] using f.isReal_of_mem w hw
    · exact absurd ((hinf w).mp hw) hneg
  -- `F ∣ f`
  obtain ⟨c, hc0, hc⟩ := exists_nat_eq_span f.finite f.finite_ne_bot
  have : NeZero c := ⟨hc0⟩
  have := CyclotomicField.isCyclotomicExtension c ℚ
  have := IsCyclotomicExtension.isAbelianGalois {c} ℚ (CyclotomicField c ℚ)
  have hclass' := cyclotomic_isClassField c hc0 (CyclotomicField c ℚ)
  have hfc : f.Dvd (ratModulus c hc0) := by
    refine ⟨by rw [hc]; exact dvd_rfl, fun w hw => ?_⟩
    exact f.isReal_of_mem w hw
  obtain ⟨g⟩ := (remark_3_8_subfield L _ _ hclass' f hf).mpr hfc
  have hnc : (discr L).natAbs ∣ c := hmin c (Nat.pos_of_ne_zero hc0) ⟨g⟩
  have hFf : (ratModulusOf (discr L).natAbs hn (decide (d < 0))).Dvd f := by
    refine ⟨?_, fun w hw => ?_⟩
    · show Ideal.span {((discr L).natAbs : 𝓞 ℚ)} ∣ f.finite
      rw [hc, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact Nat.cast_dvd_cast hnc
    · by_cases hneg : d < 0
      · exact (hinf w).mpr hneg
      · simp [ratModulusOf, hneg] at hw
  exact ⟨ArtinFactorsThrough.of_dvd L hf.1 hfF, fun m hm => modulus_dvd_trans hFf (hf.2 m hm)⟩

end Ex311

/-- **Example 3.11** (Milne, *CFT*, V, p. 159), unconditional. -/
@[kb "milne2020cft" "Ch. V, Example 3.11, p. 159"]
theorem example3_11 : Example3_11 where
  mem_cyclotomic L _ _ d s hd hd1 hs hfin := Ex311.mem_cyclotomic_aux hd hd1 hs hfin
  conductor L _ _ _ d s hd hd1 hs hfin :=
    Ex311.conductor_aux L d s hd hd1 hs hfin (by
      have : discr L ≠ 0 := discr_ne_zero L
      omega)

end NumberFieldKB.MilneCFT
