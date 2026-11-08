import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.Chebotarev.DirichletHeckeRat
import QuadFormsKB.Literature.HasseNorm.Reciprocity

/-!
# The main theorems in terms of idèles (Milne, *Class Field Theory*, Chapter V, §5, pp. 177–182)

**The global Artin map, as characterized in Summary 5.10.** Milne defines $\phi_{L/K} : I_K \to \mathrm{Gal}(L/K)$ as the
product of the local Artin maps $\phi_v : K_v^\times \to D(w) \subseteq \mathrm{Gal}(L/K)$ (Proposition 5.2). The local
Artin maps of the completions $K_v$ are not connected to the local class field theory of Chapter I in this library, so
the global map is described by the properties of Summary 5.10, which determine it (`idelicArtin_unique`):
`IsIdelicArtinMap L φ`: $\varphi$ is continuous ($\ker\varphi$ open), (a) $\varphi(u) = 1$ for every idèle $u$ that is a
unit at the finite primes unramified in $L$, close to $1$ at the ramified ones, and positive at the real primes that
become complex in $L$; (b) for $v$ unramified, $\varphi$ sends a prime element of $K_v$ (placed at $v$) to the Frobenius
element $(\mathfrak p_v, L/K)$. A product of local Artin maps has these properties (Chapter I, Theorem 1.1, and I, 1.3).

* **Lemma 5.1** (`lemma_5_1`, decomposition groups); **Proposition 5.2** (`prop_5_2`, the compatible family of maps,
  from the uniqueness);
* **Theorem 5.3** (the reciprocity law): the named statement `IdelicReciprocity`; the restatement with idèle classes
  (`theorem_5_3_classes`);
* **Example 5.4** (`example_5_4`, $n = 2$: QuadFormsKB's Hilbert reciprocity);
* **Theorem 5.5** (the existence theorem): the named statement `IdelicExistence`; norm groups and class fields
  (`normGroupC`, `IsNormGroupC`); **Corollary 5.6** (`cor_5_6`);
* **Remark 5.7** (`remark_5_7_le_ker`; named `Remark5_7`); **Remark 5.8** (named `Remark5_8`);
* Lemma 5.9 and the Artin map of $\mathbb Q(\zeta_m)$: `Ch5RatIdeles.lean`; **Summary 5.10** (`summary_5_10`);
  **Exercise 5.11** (named).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open scoped nonZeroDivisors Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## The characterization of the global Artin map (Summary 5.10) -/

/-! ## A general uniqueness statement for homomorphisms on idèles -/

theorem ideleFinAt_ofAdic_self (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v z) v = (z : v.adicCompletion K) :=
  NumberFieldKB.Ideles.finiteOfAdicCompletion_self v (z : v.adicCompletion K)

theorem ideleFinAt_ofAdic_ne {v v' : HeightOneSpectrum (𝓞 K)} (h : v' ≠ v) (z : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v z) v' = 1 :=
  NumberFieldKB.Ideles.finiteOfAdicCompletion_of_ne h (z : v.adicCompletion K)

theorem ideleInfAt_ofAdic (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) (w : InfinitePlace K) :
    ideleInfAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v z) w = 1 :=
  rfl

/-- An idèle has absolute value one at all but finitely many finite primes. -/
theorem finite_valued_ne_one (y : IdeleGroup (𝓞 K) K) :
    {v : HeightOneSpectrum (𝓞 K) | Valued.v (ideleFinAt y v) ≠ 1}.Finite := by
  have h1 := (y : AdeleRing (𝓞 K) K).2.2
  have h2 := ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2.2
  refine (Filter.eventually_cofinite.mp (h1.and h2)).subset ?_
  intro v hv ⟨hA, hB⟩
  apply hv
  have hmul : Valued.v (ideleFinAt y v) * Valued.v (ideleFinAt y⁻¹ v) = 1 := by
    rw [← map_mul]
    have h3 : ideleFinAt y v * ideleFinAt y⁻¹ v = 1 :=
      congrArg (fun a : IdeleGroup (𝓞 K) K => ideleFinAt a v) (mul_inv_cancel y)
    rw [h3, map_one]
  have hB' : Valued.v (ideleFinAt y⁻¹ v) ≤ 1 := hB
  have hA' : Valued.v (ideleFinAt y v) ≤ 1 := hA
  refine le_antisymm hA' ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (ideleFinAt y v) * Valued.v (ideleFinAt y⁻¹ v) := hmul.symm
    _ ≤ Valued.v (ideleFinAt y v) * 1 := by gcongr
    _ = _ := mul_one _

/-- A prime element of the completion at a finite prime, as a unit. -/
theorem exists_unit_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have h : Valued.v ((algebraMap (𝓞 K) K π : K) : v.adicCompletion K) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hne : ((algebraMap (𝓞 K) K π : K) : v.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  exact ⟨Units.mk0 _ hne, h⟩

/-- **Uniqueness of homomorphisms on idèles determined locally**: two homomorphisms from the idèle group to a group
that agree on the principal idèles, on the idèles that are units outside a finite set `S` of finite primes, close to
one on `S` and positive at the places in `P`, and on the prime elements at the primes outside `S`, are equal. The proof
writes an idèle as a principal idèle times an idèle of the modulus (Proposition 4.6(b)), and then clears the finitely
many non-unit components outside `S` by prime elements. -/
theorem ideleHom_eq_of_local {G : Type} [Group G] (φ ψ : IdeleGroup (𝓞 K) K →* G)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (P : InfinitePlace K → Prop)
    (hP : ∀ w, P w → w.IsReal) (n : ℕ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = ψ (IdeleGroup.unitEmbedding (𝓞 K) K a))
    (hU : ∀ u : IdeleGroup (𝓞 K) K, (∀ v ∉ S, Valued.v (ideleFinAt u v) = 1) →
      (∀ v ∈ S, Valued.v (ideleFinAt u v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ (w : InfinitePlace K) (hw : P w), IsPosAt w (hP w hw) (ideleInfAt u w)) → φ u = ψ u)
    (hπ : ∀ v ∉ S, ∀ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) →
      φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v π) = ψ (IdeleGroup.ofAdicCompletion (𝓞 K) K v π)) :
    φ = ψ := by
  classical
  -- the induction clearing the non-unit components outside `S`
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ y : IdeleGroup (𝓞 K) K,
      (∀ v ∈ S, Valued.v (ideleFinAt y v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ (w : InfinitePlace K) (hw : P w), IsPosAt w (hP w hw) (ideleInfAt y w)) →
      (∀ v ∉ S, v ∉ T → Valued.v (ideleFinAt y v) = 1) → φ y = ψ y := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro y h1 h2 h3
      exact hU y (fun v hv => h3 v hv (Finset.notMem_empty v)) h1 h2
    | insert v T hvT ih =>
      intro y h1 h2 h3
      by_cases hv : v ∉ S ∧ Valued.v (ideleFinAt y v) ≠ 1
      · obtain ⟨hvS, hv1⟩ := hv
        obtain ⟨π, hπv⟩ := exists_unit_uniformizer v
        have hy0 : ideleFinAt y v ≠ 0 := by
          have h3 : ideleFinAt y v * ideleFinAt y⁻¹ v = 1 :=
            congrArg (fun a : IdeleGroup (𝓞 K) K => ideleFinAt a v) (mul_inv_cancel y)
          exact left_ne_zero_of_mul_eq_one h3
        have hne : Valued.v (ideleFinAt y v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
        set k : ℤ := WithZero.log (Valued.v (ideleFinAt y v)) with hk
        have hkv : Valued.v (ideleFinAt y v) = WithZero.exp k := (WithZero.exp_log hne).symm
        set z := IdeleGroup.ofAdicCompletion (𝓞 K) K v (π ^ k) with hz
        have hzv : ideleFinAt z v = ((π ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
          ideleFinAt_ofAdic_self v _
        have hval : Valued.v (ideleFinAt (y * z) v) = 1 := by
          have : ideleFinAt (y * z) v = ideleFinAt y v * ideleFinAt z v := rfl
          rw [this, map_mul, hzv, Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, hkv, ← WithZero.exp_zsmul,
            ← WithZero.exp_add]
          simp
        have hyz : φ (y * z) = ψ (y * z) := by
          refine ih (y * z) ?_ ?_ ?_
          · intro v' hv'
            have hne : v' ≠ v := fun h => hvS (h ▸ hv')
            have : ideleFinAt (y * z) v' = ideleFinAt y v' * ideleFinAt z v' := rfl
            rw [this, ideleFinAt_ofAdic_ne hne, mul_one]
            exact h1 v' hv'
          · intro w hw
            have : ideleInfAt (y * z) w = ideleInfAt y w * ideleInfAt z w := rfl
            rw [this, ideleInfAt_ofAdic, mul_one]
            exact h2 w hw
          · intro v' hv'S hv'T
            by_cases hvv : v' = v
            · subst hvv; exact hval
            · have : ideleFinAt (y * z) v' = ideleFinAt y v' * ideleFinAt z v' := rfl
              rw [this, ideleFinAt_ofAdic_ne hvv, mul_one]
              exact h3 v' hv'S (by simp [hvv, hv'T])
        have hzz : φ z = ψ z := by
          simp only [hz, map_zpow, hπ v hvS π hπv]
        rw [map_mul, map_mul, hzz] at hyz
        exact mul_right_cancel hyz
      · refine ih y h1 h2 (fun v' hv'S hv'T => ?_)
        by_cases hvv : v' = v
        · subst hvv
          by_contra hcon
          exact hv ⟨hv'S, hcon⟩
        · exact h3 v' hv'S (by simp [hvv, hv'T])
  -- the modulus
  let I : Ideal (𝓞 K) := ∏ v ∈ hS.toFinset, v.asIdeal ^ (n + 1)
  have hI : I ≠ ⊥ := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  let m : Modulus K := ⟨I, hI, {w | P w}, fun w hw => hP w hw⟩
  have hdvd : ∀ v ∈ S, v.asIdeal ^ (n + 1) ∣ I := fun v hv =>
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ (n + 1)) (hS.mem_toFinset.mpr hv)
  have hord : ∀ v ∈ S, v ∈ m.finiteSupport ∧ n ≤ m.ord v := by
    intro v hv
    refine ⟨(dvd_pow_self v.asIdeal (Nat.succ_ne_zero n)).trans (hdvd v hv), ?_⟩
    have h1 : Associates.mk v.asIdeal ^ (n + 1) ≤ Associates.mk I := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hdvd v hv
    have hI' : Associates.mk (I : Ideal (𝓞 K)) ≠ 0 := Associates.mk_ne_zero.mpr hI
    have := (Associates.prime_pow_dvd_iff_le hI' v.associates_irreducible).mp h1
    show n ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors
    omega
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := (prop_4_6b m).1 (x : IdeleClassGroup (𝓞 K) K)
  obtain ⟨a, ha⟩ := (QuotientGroup.eq.mp hy)
  have hx : x = (y : IdeleGroup (𝓞 K) K) * IdeleGroup.unitEmbedding (𝓞 K) K a := by
    rw [ha]; simp
  have hyy : φ (y : IdeleGroup (𝓞 K) K) = ψ (y : IdeleGroup (𝓞 K) K) := by
    refine key (finite_valued_ne_one (y : IdeleGroup (𝓞 K) K)).toFinset y ?_ ?_ ?_
    · intro v hv
      obtain ⟨hv1, hv2⟩ := hord v hv
      refine (y.2.2 v hv1).trans (WithZero.exp_le_exp.mpr ?_)
      have : (n : ℤ) ≤ (m.ord v : ℤ) := by exact_mod_cast hv2
      omega
    · intro w hw
      exact y.2.1 w hw
    · intro v _ hvT
      by_contra hcon
      exact hvT ((finite_valued_ne_one (y : IdeleGroup (𝓞 K) K)).mem_toFinset.mpr hcon)
  rw [hx, map_mul, map_mul, hyy, hK a]


section Characterization

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The properties (a), (b) of Summary 5.10** (Milne, *CFT*, V, p. 181) of a homomorphism
$\varphi : I_K \to \mathrm{Gal}(L/K)$; see the module docstring. -/
@[kb "milne2020cft" "Ch. V, Summary 5.10 (properties (a), (b))"]
structure IsIdelicArtinMap (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) : Prop where
  isOpen_ker : IsOpen (φ.ker : Set (IdeleGroup (𝓞 K) K))
  local_ramified : ∃ n : ℕ, ∀ u : IdeleGroup (𝓞 K) K,
    (∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L → Valued.v (ideleFinAt u v) = 1) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ unramifiedPrimes K L →
      Valued.v (ideleFinAt u v - 1) ≤ WithZero.exp (-(n : ℤ))) →
    (∀ (w : InfinitePlace K) (hw : w.IsReal), InfinitePlace.RamifiesIn L w → IsPosAt w hw (ideleInfAt u w)) →
    φ u = 1
  frobenius : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L → ∀ π : (v.adicCompletion K)ˣ,
    Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) →
    φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v π) = artinFrob L v

/-- **Uniqueness in Summary 5.10** (Milne, *CFT*, V, p. 181): there is at most one homomorphism
$I_K \to \mathrm{Gal}(L/K)$ with the properties (a), (b) that is trivial on $K^\times$ (weak approximation). -/
@[kb "milne2020cft" "Ch. V, Summary 5.10 (uniqueness)"]
theorem idelicArtin_unique (φ ψ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hψ : IsIdelicArtinMap L ψ) (hφK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hψK : ∀ a : Kˣ, ψ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) : φ = ψ := by
  obtain ⟨nφ, hnφ⟩ := hφ.local_ramified
  obtain ⟨nψ, hnψ⟩ := hψ.local_ramified
  refine ideleHom_eq_of_local φ ψ (unramifiedPrimes K L)ᶜ (finite_compl_unramifiedPrimes K L)
    (InfinitePlace.RamifiesIn L) (fun w hw => hw.1) (max nφ nψ) (fun a => by rw [hφK, hψK]) ?_ ?_
  · intro u h1 h2 h3
    have hu1 : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L → Valued.v (ideleFinAt u v) = 1 :=
      fun v hv => h1 v (not_not.mpr hv)
    rw [hnφ u hu1 (fun v hv => (h2 v hv).trans (WithZero.exp_le_exp.mpr (by omega)))
      (fun w hw hr => h3 w hr), hnψ u hu1 (fun v hv => (h2 v hv).trans (WithZero.exp_le_exp.mpr (by omega)))
      (fun w hw hr => h3 w hr)]
  · intro v hv π hπ
    rw [hφ.frobenius v (not_not.mp hv) π hπ, hψ.frobenius v (not_not.mp hv) π hπ]

/-- The norm group $K^\times\cdot\mathrm{Nm}_{L/K}(I_L) \subseteq I_K$. -/
def ideleNormGroup (L : Type) [Field L] [NumberField L] [Algebra K L] : Subgroup (IdeleGroup (𝓞 K) K) :=
  IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (ideleNormMap K L : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K).range

end Characterization

/-! ## Theorem 5.3, the reciprocity law -/

variable (K) in
/-- **Theorem 5.3, the reciprocity law** (named statement; Milne, *CFT*, V, Theorem 5.3, p. 178, with Proposition 5.2;
proved in Chapter VII): for every finite abelian extension $L/K$ the global Artin map
$\phi_{L/K} : I_K \to \mathrm{Gal}(L/K)$ (with the properties of Summary 5.10) satisfies (a) $\phi_{L/K}(K^\times) = 1$,
and (b) it induces $I_K/K^\times\cdot\mathrm{Nm}(I_L) \cong \mathrm{Gal}(L/K)$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.ker_ideleClassArtinMap` (`TauCeti/NumberTheory/ClassFieldTheory/Global/Reciprocity.lean:281`),
`TauCeti.ClassFieldTheory.ideleClassArtinMap_surjective` (same file, line 293),
`TauCeti.ClassFieldTheory.globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean:108`) and
`TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap`
(`TauCeti/NumberTheory/NumberField/Global/Ideles/Norm/Open.lean:118`) at Tau Ceti commit `7ed979dc`. Needed to apply
it here: take our homomorphism to be Tau Ceti's Artin map on the idele class group composed with the quotient map from
the ideles, so that its kernel is the preimage of the norm group of the idele class group, which is
$K^\times\cdot\mathrm{Nm}(I_L)$. The clause about ramified places in our structure follows from openness of the
kernel. One must also identify our idele group and idele class group with Tau Ceti's. -/
@[kb "milne2020cft" "Ch. V, Theorem 5.3 (input)"]
structure IdelicReciprocity : Prop where
  exists_artin : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    ∃ φ : IdeleGroup (𝓞 K) K →* Gal(L/K), IsIdelicArtinMap L φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      Function.Surjective φ ∧ φ.ker = ideleNormGroup L

/-- The norm group $\mathrm{Nm}(C_L) \subseteq C_K$ of idèle classes (Milne, *CFT*, V, §5, p. 179). -/
@[kb "milne2020cft" "Ch. V, §5, p. 179 (the norm group Nm(C_L))"]
def normGroupC (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L] :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (Ideles.ideleClassRelNorm (Module.finBasis K L) : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range

section ClassArtin

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- The idèlic Artin map of $L/K$ given by Theorem 5.3 (a choice). -/
def idelicArtinOf : IdeleGroup (𝓞 K) K →* Gal(L/K) := (hR.exists_artin L).choose

theorem idelicArtinOf_spec : IsIdelicArtinMap L (idelicArtinOf hR L) ∧
    (∀ a : Kˣ, idelicArtinOf hR L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
    Function.Surjective (idelicArtinOf hR L) ∧ (idelicArtinOf hR L).ker = ideleNormGroup L :=
  (hR.exists_artin L).choose_spec

/-- The map on idèle classes induced by `idelicArtinOf`. -/
def classArtinOf : IdeleClassGroup (𝓞 K) K →* Gal(L/K) :=
  QuotientGroup.lift _ (idelicArtinOf hR L) (by
    rintro _ ⟨a, rfl⟩
    exact (idelicArtinOf_spec hR L).2.1 a)

theorem classArtinOf_mk (x : IdeleGroup (𝓞 K) K) :
    classArtinOf hR L (x : IdeleClassGroup (𝓞 K) K) = idelicArtinOf hR L x := rfl

theorem classArtinOf_surjective : Function.Surjective (classArtinOf hR L) := by
  intro σ
  obtain ⟨x, rfl⟩ := (idelicArtinOf_spec hR L).2.2.1 σ
  exact ⟨(x : IdeleClassGroup (𝓞 K) K), rfl⟩

theorem ker_classArtinOf : (classArtinOf hR L).ker = normGroupC K L := by
  have hker := (idelicArtinOf_spec hR L).2.2.2
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [MonoidHom.mem_ker, classArtinOf_mk]
  rw [← MonoidHom.mem_ker, hker, ideleNormGroup]
  constructor
  · intro hx
    obtain ⟨a, ha, n, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
    refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
    refine (Ideles.ideleClassRelNorm_mk _ y).trans ?_
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha]
    exact (one_mul (M := IdeleClassGroup (𝓞 K) K) _).symm
  · rintro ⟨c', hc'⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c'
    have hp := QuotientGroup.eq.mp ((Ideles.ideleClassRelNorm_mk _ y).symm.trans hc')
    have hr : ideleNormMap K L y ∈
        (ideleNormMap K L : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K).range :=
      MonoidHom.mem_range.mpr ⟨y, rfl⟩
    have hmem := Subgroup.mul_mem_sup hp hr
    have e : ((ideleNormMap K L y)⁻¹ * x) * ideleNormMap K L y = x := by
      rw [mul_comm ((ideleNormMap K L y)⁻¹) x, mul_assoc, inv_mul_cancel, mul_one]
    exact e ▸ hmem

include hR in
theorem isOpen_normGroupC : IsOpen (normGroupC K L : Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [← ker_classArtinOf hR L]
  refine (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.mp ?_
  have : (QuotientGroup.mk ⁻¹' ((classArtinOf hR L).ker : Set (IdeleClassGroup (𝓞 K) K))) =
      ((idelicArtinOf hR L).ker : Set (IdeleGroup (𝓞 K) K)) := by
    ext x
    simp [classArtinOf_mk]
  rw [this]
  exact (idelicArtinOf_spec hR L).1.isOpen_ker

include hR in
theorem finiteIndex_normGroupC : (normGroupC K L).FiniteIndex := by
  rw [← ker_classArtinOf hR L]
  infer_instance

end ClassArtin

/-- **Theorem 5.3(b), with idèle classes** (Milne, *CFT*, V, p. 179): $\phi_{L/K}$ induces
$C_K/\mathrm{Nm}(C_L) \cong \mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 5.3 (C_K/Nm(C_L) ≅ Gal(L/K))"]
theorem theorem_5_3_classes (h : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    ∃ φ : IdeleClassGroup (𝓞 K) K →* Gal(L/K), Function.Surjective φ ∧ φ.ker = normGroupC K L :=
  ⟨classArtinOf h L, classArtinOf_surjective h L, ker_classArtinOf h L⟩

/-- If `a` is within `exp (-n)` of one, with `n ≥ 1`, then `a` has absolute value one. -/
theorem valued_eq_one_of_sub_le_exp {F : Type*} [Field F] {v : Valuation F (WithZero (Multiplicative ℤ))} {a : F}
    {n : ℕ} (h : v (a - 1) ≤ WithZero.exp (-(n : ℤ))) (hn : 1 ≤ n) : v a = 1 := by
  have hlt : v (a - 1) < 1 := by
    refine lt_of_le_of_lt h ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have := Valuation.map_eq_of_sub_lt v (x := 1) (y := a) (by simpa using hlt)
  simpa using this

/-! ### Compatibility of ramification and Frobenius elements in a tower of abelian extensions -/

section Compatibility

variable {Ω : Type} [Field Ω] [Algebra K Ω] (L M : IntermediateField K Ω) [NumberField L] [NumberField M]
  [IsAbelianGalois K L] [IsAbelianGalois K M]

/-- A real place that ramifies in $L$ ramifies in every larger field $M$. -/
theorem ramifiesIn_of_le (hLM : L ≤ M) (w : InfinitePlace K) (h : InfinitePlace.RamifiesIn L w) :
    InfinitePlace.RamifiesIn M w := by
  let _ : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have : Algebra.IsAlgebraic L M := Algebra.IsAlgebraic.tower_top (K := K) L
  obtain ⟨wL, hwL, hc⟩ := h.2
  obtain ⟨wM, hwM⟩ := InfinitePlace.comap_surjective (k := L) (K := M) wL
  have hwM' : wM.comap (algebraMap L M) = wL := hwM
  refine ⟨h.1, wM, ?_, InfinitePlace.IsComplex.of_comap (algebraMap L M) (hwM' ▸ hc)⟩
  rw [IsScalarTower.algebraMap_eq K L M, InfinitePlace.comap_comp, hwM', hwL]

open scoped IsMulCommutative in
/-- The Frobenius element of an unramified prime restricts to the Frobenius element in the subextension. -/
theorem galRestrict_artinFrob (hLM : L ≤ M) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K M) :
    LocalCFT.galRestrict hLM (artinFrob M v) = artinFrob L v := by
  let _ : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have h := frobClass_restrict K L M hv
  rw [frobClass_eq_mk_frobAt K L v (Classical.arbitrary _), frobClass_eq_mk_frobAt K M v (Classical.arbitrary _)]
    at h
  have h' : ConjClasses.mk (frobAt K L v (Classical.arbitrary _)) =
      ConjClasses.mk (AlgEquiv.restrictNormalHom L (frobAt K M v (Classical.arbitrary _))) := h
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h'
  exact h'.symm

end Compatibility

/-- **Proposition 5.2** (Milne, *CFT*, V, p. 178; see the module docstring for the form): for $L \subseteq M$ finite
abelian over $K$ (inside a common field $\Omega$), the Artin maps are compatible with restriction,
$\phi_{M/K}(a)|_L = \phi_{L/K}(a)$, so they define one continuous homomorphism $I_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$.
Proved unconditionally from the uniqueness in Summary 5.10 (the existence of the maps is Theorem 5.3). -/
@[kb "milne2020cft" "Ch. V, Proposition 5.2"]
theorem prop_5_2 (Ω : Type) [Field Ω] [Algebra K Ω]
    (L M : IntermediateField K Ω) [NumberField L] [NumberField M] [IsAbelianGalois K L] [IsAbelianGalois K M]
    (hLM : L ≤ M) (φL : IdeleGroup (𝓞 K) K →* Gal(L/K)) (φM : IdeleGroup (𝓞 K) K →* Gal(M/K))
    (hL : IsIdelicArtinMap L φL) (hM : IsIdelicArtinMap M φM)
    (hLK : ∀ a : Kˣ, φL (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hMK : ∀ a : Kˣ, φM (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) (x : IdeleGroup (𝓞 K) K) :
    LocalCFT.galRestrict hLM (φM x) = φL x := by
  let _ : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  obtain ⟨nL, hnL⟩ := hL.local_ramified
  obtain ⟨nM, hnM⟩ := hM.local_ramified
  have hmain : (LocalCFT.galRestrict hLM).comp φM = φL := by
    refine ideleHom_eq_of_local _ φL (unramifiedPrimes K M)ᶜ (finite_compl_unramifiedPrimes K M)
      (InfinitePlace.RamifiesIn M) (fun w hw => hw.1) (max (max nL nM) 1)
      (fun a => by rw [MonoidHom.comp_apply, hMK, map_one, hLK]) ?_ ?_
    · intro u h1 h2 h3
      have hM1 : φM u = 1 := hnM u (fun v hv => h1 v (not_not.mpr hv))
        (fun v hv => (h2 v hv).trans (WithZero.exp_le_exp.mpr (by omega))) (fun w hw hr => h3 w hr)
      have hL1 : φL u = 1 := by
        refine hnL u (fun v hv => ?_) (fun v hv => ?_) (fun w hw hr => h3 w (ramifiesIn_of_le L M hLM w hr))
        · by_cases hvM : v ∈ unramifiedPrimes K M
          · exact h1 v (not_not.mpr hvM)
          · exact valued_eq_one_of_sub_le_exp (h2 v hvM) (by omega)
        · have hvM : v ∉ unramifiedPrimes K M := fun h => hv (unramifiedPrimes_subset_of_tower K L M h)
          exact (h2 v hvM).trans (WithZero.exp_le_exp.mpr (by omega))
      rw [MonoidHom.comp_apply, hM1, map_one, hL1]
    · intro v hv π hπ
      have hvM : v ∈ unramifiedPrimes K M := not_not.mp hv
      rw [MonoidHom.comp_apply, hM.frobenius v hvM π hπ, galRestrict_artinFrob L M hLM v hvM,
        hL.frobenius v (unramifiedPrimes_subset_of_tower K L M hvM) π hπ]
  exact DFunLike.congr_fun hmain x

/-- **Lemma 5.1, decomposition groups** (Milne, *CFT*, V, p. 177): for $L/K$ abelian, the decomposition group
$D(\mathfrak P) = \{\sigma : \sigma\mathfrak P = \mathfrak P\}$ does not depend on the prime $\mathfrak P$ above
$\mathfrak p$. (The second claim, on the local Artin maps of the completions, is outside the library's local class
field theory; see the module docstring.) -/
@[kb "milne2020cft" "Ch. V, Lemma 5.1 (decomposition group)"]
theorem lemma_5_1 (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (P Q : v.asIdeal.primesOver (𝓞 L)) :
    MulAction.stabilizer Gal(L/K) P.1 = MulAction.stabilizer Gal(L/K) Q.1 := by
  have := P.2.1; have := P.2.2; have := Q.2.1; have := Q.2.2
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal P.1 Q.1 Gal(L/K)
  have hc : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  rw [← hσ, MilneANT.item_8_14_stabilizer]
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨g, h, by rw [hc σ g, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [hc σ x, mul_inv_cancel_right]

section NormGroups

variable (hR : IdelicReciprocity K) {Ω : Type} [Field Ω] [Algebra K Ω]
  (L M : IntermediateField K Ω) [NumberField L] [NumberField M] [IsAbelianGalois K L] [IsAbelianGalois K M]

include hR

/-- The class-group Artin maps are compatible with restriction (Proposition 5.2). -/
theorem classArtinOf_restrict (hLM : L ≤ M) (c : IdeleClassGroup (𝓞 K) K) :
    LocalCFT.galRestrict hLM (classArtinOf hR M c) = classArtinOf hR L c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  exact prop_5_2 Ω L M hLM _ _ (idelicArtinOf_spec hR L).1 (idelicArtinOf_spec hR M).1
    (idelicArtinOf_spec hR L).2.1 (idelicArtinOf_spec hR M).2.1 x

/-- Norm groups reverse inclusions of fields. -/
theorem normGroupC_antitone (hLM : L ≤ M) : normGroupC K M ≤ normGroupC K L := by
  intro c hc
  rw [← ker_classArtinOf hR M, MonoidHom.mem_ker] at hc
  rw [← ker_classArtinOf hR L, MonoidHom.mem_ker, ← classArtinOf_restrict hR L M hLM, hc, map_one]

/-- Nested abelian fields with the same norm group are equal. -/
theorem eq_of_normGroupC_eq (hLM : L ≤ M) (h : normGroupC K L = normGroupC K M) : L = M := by
  have hinj : Function.Injective (LocalCFT.galRestrict hLM) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    obtain ⟨c, rfl⟩ := classArtinOf_surjective hR M g
    rw [MonoidHom.mem_ker, classArtinOf_restrict] at hg
    have hc : c ∈ normGroupC K L := by rw [← ker_classArtinOf hR L]; exact hg
    rw [h, ← ker_classArtinOf hR M] at hc
    simpa using hc
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at hc
  exact IntermediateField.eq_of_le_of_finrank_le hLM hc

end NormGroups

section SupInf

variable (hR : IdelicReciprocity K) {Ω : Type} [Field Ω] [Algebra K Ω]
  (L M : IntermediateField K Ω) [NumberField L] [NumberField M] [IsAbelianGalois K L] [IsAbelianGalois K M]

/-- The kernel of the restriction map to a normal subfield is the fixing subgroup of that subfield. -/
theorem ker_galRestrict_eq (A F : IntermediateField K Ω) [Normal K A] (h : A ≤ F) :
    (LocalCFT.galRestrict h).ker = (IntermediateField.restrict h : IntermediateField K F).fixingSubgroup := by
  let _ : Algebra A F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower K A F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have e := AlgEquiv.ker_restrictNormalHom (F := K) (K₁ := F) A
  have e2 : (IsScalarTower.toAlgHom K A F).fieldRange = (IntermediateField.restrict h : IntermediateField K F) := by
    ext x
    simp only [AlgHom.mem_fieldRange, IntermediateField.mem_restrict]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, rfl⟩
  rw [e2] at e
  exact e

include hR

theorem normGroupC_sup [NumberField ↥(L ⊔ M)] :
    normGroupC K ↥(L ⊔ M) = normGroupC K L ⊓ normGroupC K M := by
  refine le_antisymm (le_inf (normGroupC_antitone hR L _ le_sup_left)
    (normGroupC_antitone hR M _ le_sup_right)) ?_
  intro c hc
  have h1 : c ∈ normGroupC K L := hc.1
  have h2 : c ∈ normGroupC K M := hc.2
  rw [← ker_classArtinOf hR, MonoidHom.mem_ker] at h1 h2 ⊢
  refine IntermediateField.restrictNormalHomSupProd_injective L M ?_
  rw [map_one]
  refine Prod.ext ?_ ?_
  · exact (classArtinOf_restrict hR L (L ⊔ M) le_sup_left c).trans h1
  · exact (classArtinOf_restrict hR M (L ⊔ M) le_sup_right c).trans h2

open scoped IsMulCommutative in
theorem normGroupC_inf [NumberField ↥(L ⊔ M)] [NumberField ↥(L ⊓ M)] [IsAbelianGalois K ↥(L ⊓ M)] :
    normGroupC K ↥(L ⊓ M) = normGroupC K L ⊔ normGroupC K M := by
  refine le_antisymm ?_ (sup_le (normGroupC_antitone hR _ L inf_le_left)
    (normGroupC_antitone hR _ M inf_le_right))
  intro c hc
  have hker : (LocalCFT.galRestrict (inf_le_left.trans le_sup_left : L ⊓ M ≤ L ⊔ M)).ker =
      (LocalCFT.galRestrict (le_sup_left : L ≤ L ⊔ M)).ker ⊔
        (LocalCFT.galRestrict (le_sup_right : M ≤ L ⊔ M)).ker := by
    rw [ker_galRestrict_eq, ker_galRestrict_eq, ker_galRestrict_eq]
    have hlift : (IntermediateField.restrict (inf_le_left.trans le_sup_left : L ⊓ M ≤ L ⊔ M) :
        IntermediateField K ↥(L ⊔ M)) =
        IntermediateField.restrict (le_sup_left : L ≤ L ⊔ M) ⊓ IntermediateField.restrict (le_sup_right : M ≤ L ⊔ M) := by
      refine IntermediateField.lift_injective (L ⊔ M) ?_
      rw [IntermediateField.lift_inf, IntermediateField.lift_restrict, IntermediateField.lift_restrict,
        IntermediateField.lift_restrict]
    rw [hlift]
    exact (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := ↥(L ⊔ M))).map_inf _ _
  have hg : classArtinOf hR ↥(L ⊔ M) c ∈
      (LocalCFT.galRestrict (inf_le_left.trans le_sup_left : L ⊓ M ≤ L ⊔ M)).ker := by
    rw [MonoidHom.mem_ker, classArtinOf_restrict hR (L ⊓ M) (L ⊔ M), ← MonoidHom.mem_ker,
      ker_classArtinOf hR]
    exact hc
  rw [hker] at hg
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := Subgroup.mem_sup.mp hg
  obtain ⟨c₁, rfl⟩ := classArtinOf_surjective hR ↥(L ⊔ M) h₁
  obtain ⟨c₂, rfl⟩ := classArtinOf_surjective hR ↥(L ⊔ M) h₂
  have hc₁ : c₁ ∈ normGroupC K L := by
    rw [← ker_classArtinOf hR, MonoidHom.mem_ker, ← classArtinOf_restrict hR L (L ⊔ M) le_sup_left]
    exact hh₁
  have hc₂ : c₂ ∈ normGroupC K M := by
    rw [← ker_classArtinOf hR, MonoidHom.mem_ker, ← classArtinOf_restrict hR M (L ⊔ M) le_sup_right]
    exact hh₂
  have hc' : c * (c₁ * c₂)⁻¹ ∈ normGroupC K ↥(L ⊔ M) := by
    rw [← ker_classArtinOf hR, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hprod, mul_inv_cancel]
  have hc'' := normGroupC_antitone hR L (L ⊔ M) le_sup_left hc'
  have : c = c * (c₁ * c₂)⁻¹ * (c₁ * c₂) := by rw [inv_mul_cancel_right]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc'')
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₁) (Subgroup.mem_sup_right hc₂))

end SupInf

/-- **Example 5.4** (Milne, *CFT*, V, p. 179, for $n = 2$): Theorem 5.3(a) for $K(\sqrt a)/K$ gives the product formula
for the Hilbert symbol, $\prod_v (a,b)_v = 1$ for $a, b \in K^\times$; proved in QuadFormsKB without class field theory
(`QuadFormsKB.HN.hilbert_product_formula_nf`). The case of general $n$ (with $\mu_n \subseteq K$) needs the $n$-th power
Hilbert symbol, not in the library. -/
@[kb "milne2020cft" "Ch. V, Example 5.4 (n = 2)"]
theorem example_5_4 (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : QuadFormsKB.NFPlace K | v.hilbert a b = -1}.Finite ∧
      Even {v : QuadFormsKB.NFPlace K | v.hilbert a b = -1}.ncard :=
  QuadFormsKB.HN.hilbert_product_formula_nf a b ha hb

/-! ## Theorem 5.5, the existence theorem -/

/-- **Norm groups** (Milne, *CFT*, V, §5, p. 179): the subgroups of $C_K$ of the form $\mathrm{Nm}(C_L)$, $L$ finite abelian
over $K$. -/
@[kb "milne2020cft" "Ch. V, §5, p. 179 (norm group)"]
def IsNormGroupC (N : Subgroup (IdeleClassGroup (𝓞 K) K)) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L), normGroupC K L = N

/-- **The class field belonging to $N$** (Milne, *CFT*, V, §5, p. 179): a finite abelian $L/K$ with
$\mathrm{Nm}(C_L) = N$. -/
@[kb "milne2020cft" "Ch. V, §5, p. 179 (class field belonging to N)"]
def IsClassFieldBelongingTo (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (N : Subgroup (IdeleClassGroup (𝓞 K) K)) : Prop :=
  normGroupC K L = N

variable (K) in
/-- **Theorem 5.5, the existence theorem** (named statement; Milne, *CFT*, V, Theorem 5.5, p. 179; proved in
Chapter VII): for every open subgroup $N \subseteq C_K$ of finite index there is a unique (up to $K$-isomorphism) finite
abelian extension $L/K$ with $\mathrm{Nm}(C_L) = N$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.globalAbelianExistence`
(`TauCeti/NumberTheory/ClassFieldTheory/GlobalExistence/Existence.lean:213`),
`TauCeti.ClassFieldTheory.globalClassField_unique`
(`TauCeti/NumberTheory/ClassFieldTheory/GlobalExistence/NormLimitation.lean:84`) and
`TauCeti.ClassFieldTheory.range_ideleClassNormMap_le_iff_nonempty_algHom` (same file, line 97) at Tau Ceti commit
`7ed979dc`. Needed to apply it here: Tau Ceti produces the class field as a layer of the absolute Galois group, which
must be converted to an abstract finite abelian extension of `K`; uniqueness up to isomorphism follows from the
last theorem applied in both directions. -/
@[kb "milne2020cft" "Ch. V, Theorem 5.5 (input)"]
structure IdelicExistence : Prop where
  exists_field : ∀ N : Subgroup (IdeleClassGroup (𝓞 K) K), IsOpen (N : Set (IdeleClassGroup (𝓞 K) K)) →
    N.FiniteIndex → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      normGroupC K L = N
  unique : ∀ (L L' : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L']
    [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'], normGroupC K L = normGroupC K L' → Nonempty (L ≃ₐ[K] L')

/-- **Corollary 5.6** (Milne, *CFT*, V, p. 179; proved from Theorems 5.3 and 5.5): for finite abelian extensions
$L_1, L_2$ of $K$ inside a common field, $L_1 \subseteq L_2 \iff \mathrm{Nm}(C_{L_1}) \supseteq \mathrm{Nm}(C_{L_2})$,
$\mathrm{Nm}(C_{L_1L_2}) = \mathrm{Nm}(C_{L_1}) \cap \mathrm{Nm}(C_{L_2})$, $\mathrm{Nm}(C_{L_1\cap L_2}) =
\mathrm{Nm}(C_{L_1})\cdot\mathrm{Nm}(C_{L_2})$; and $L \mapsto \mathrm{Nm}(C_L)$ maps the finite abelian extensions onto
the open subgroups of finite index (injectively up to isomorphism, Theorem 5.5). -/
@[kb "milne2020cft" "Ch. V, Corollary 5.6"]
theorem cor_5_6 (hR : IdelicReciprocity K) (hE : IdelicExistence K) (Ω : Type) [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) [NumberField L₁] [NumberField L₂] [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂] [NumberField ↥(L₁ ⊔ L₂)] [NumberField ↥(L₁ ⊓ L₂)] [IsAbelianGalois K ↥(L₁ ⊓ L₂)] :
    (L₁ ≤ L₂ ↔ normGroupC K L₂ ≤ normGroupC K L₁) ∧
      normGroupC K ↥(L₁ ⊔ L₂) = normGroupC K L₁ ⊓ normGroupC K L₂ ∧
      normGroupC K ↥(L₁ ⊓ L₂) = normGroupC K L₁ ⊔ normGroupC K L₂ ∧
      (∀ N : Subgroup (IdeleClassGroup (𝓞 K) K), (IsOpen (N : Set (IdeleClassGroup (𝓞 K) K)) ∧ N.FiniteIndex) ↔
        IsNormGroupC N) := by
  refine ⟨⟨fun h => normGroupC_antitone hR L₁ L₂ h, fun h => ?_⟩, normGroupC_sup hR L₁ L₂,
    normGroupC_inf hR L₁ L₂, fun N => ⟨fun ⟨ho, hf⟩ => ?_, ?_⟩⟩
  · have hsup : normGroupC K ↥(L₁ ⊔ L₂) = normGroupC K L₂ := by
      rw [normGroupC_sup hR, inf_eq_right.mpr h]
    have := eq_of_normGroupC_eq hR L₂ (L₁ ⊔ L₂) le_sup_right hsup.symm
    exact le_sup_left.trans this.symm.le
  · obtain ⟨L, i1, i2, i3, i4, hL⟩ := hE.exists_field N ho hf
    exact ⟨L, i1, i2, i3, i4, hL⟩
  · rintro ⟨L, _, _, _, _, rfl⟩
    exact ⟨isOpen_normGroupC hR L, finiteIndex_normGroupC hR L⟩

/-! ## Remarks 5.7 and 5.8 -/

/-- $\prod_{v\mid\infty}K_v^+$: the idèles with $a_v = 1$ at the finite primes and $a_v$ in the identity component of
$K_v^\times$ at the infinite ones ($a_v > 0$ at real $v$, no condition at complex $v$); the library's `idelesInfPos`. -/
@[kb "milne2020cft" "Ch. V, Remark 5.7 (the subgroup ∏_{v|∞} K_v^+)"]
theorem idelesInfPos_def (x : IdeleGroup (𝓞 K) K) :
    x ∈ idelesInfPos K ↔ (∀ v, ideleFinAt x v = 1) ∧
      ∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w) :=
  Iff.rfl

/-- **Remark 5.7(a), the easy inclusion** (Milne, *CFT*, V, p. 179): the kernel of $\phi_{L/K}$ contains the closure of
$K^\times\cdot\prod_{v\mid\infty}K_v^+$. -/
@[kb "milne2020cft" "Ch. V, Remark 5.7(a) (the kernel contains the closure of K^× ∏ K_v^+)"]
theorem remark_5_7_le_ker (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) :
    closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) : Set (IdeleGroup (𝓞 K) K)) ⊆
      φ.ker := by
  refine closure_minimal ?_ (Subgroup.isClosed_of_isOpen _ hφ.isOpen_ker)
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := ha
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hK c, one_mul]
  obtain ⟨n, hn⟩ := hφ.local_ramified
  refine hn b ?_ ?_ ?_
  · intro v _
    rw [(idelesInfPos_def b).mp hb |>.1 v]
    simp
  · intro v _
    rw [(idelesInfPos_def b).mp hb |>.1 v]
    simp
  · exact fun w hw _ => ((idelesInfPos_def b).mp hb).2 w hw

variable (K) in
/-- **Remark 5.7(a)** (named statement; Milne, *CFT*, V, Remark 5.7(a), p. 179): for a number field the global Artin map
$I_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ is onto (every compatible family of elements of the $\mathrm{Gal}(L/K)$ is
attained), its kernel is the closure of $K^\times\cdot\prod_{v\mid\infty}K_v^+$, and the image of that closure in $C_K$
is the identity component of $C_K$. -/
@[kb "milne2020cft" "Ch. V, Remark 5.7(a) (input)"]
structure Remark5_7 : Prop where
  surjective : ∀ (Ω : Type) [Field Ω] [Algebra K Ω]
    (φ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IdeleGroup (𝓞 K) K →* Gal(L/K)),
    (∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IsIdelicArtinMap L (φ L) ∧
      ∀ a : Kˣ, φ L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) →
    ∀ σ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], Gal(L/K),
      (∀ (L M : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L] [NumberField M]
        [IsAbelianGalois K M] (h : L ≤ M), LocalCFT.galRestrict h (σ M) = σ L) →
      ∃ x : IdeleGroup (𝓞 K) K, ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L],
        φ L x = σ L
  ker_eq : ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (φ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IdeleGroup (𝓞 K) K →* Gal(L/K)),
    (∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IsIdelicArtinMap L (φ L) ∧
      ∀ a : Kˣ, φ L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) →
    ∀ x : IdeleGroup (𝓞 K) K, (∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], φ L x = 1) ↔
      x ∈ closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) :
        Set (IdeleGroup (𝓞 K) K))
  connectedComponent : (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) ''
      closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) : Set (IdeleGroup (𝓞 K) K)) =
    connectedComponent (1 : IdeleClassGroup (𝓞 K) K)

variable (K) in
/-- **Remark 5.8** (named statement; Milne, *CFT*, V, Remark 5.8, p. 180, "a straightforward exercise"): the idèlic
theorems give the ideal-theoretic ones: Theorems 5.3 and 5.5 imply Theorems 3.5 and 3.6 (with the Artin isomorphism). -/
@[kb "milne2020cft" "Ch. V, Remark 5.8 (input)"]
structure Remark5_8 : Prop where
  reciprocity : IdelicReciprocity K → ReciprocityLaw K
  existence : IdelicReciprocity K → IdelicExistence K → ExistenceTheoremArtin K

/-- **Summary 5.10** (Milne, *CFT*, V, p. 181; from Theorem 5.3 and the uniqueness): for every finite abelian $L/K$
there is exactly one homomorphism $\phi_{L/K} : I_K \to \mathrm{Gal}(L/K)$ with the properties (a), (b) that is trivial on
$K^\times$; it is onto and induces $I_K/K^\times\cdot\mathrm{Nm}(I_L) \cong \mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. V, Summary 5.10"]
theorem summary_5_10 (h : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    ∃! φ : IdeleGroup (𝓞 K) K →* Gal(L/K), IsIdelicArtinMap L φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧ Function.Surjective φ ∧
      φ.ker = ideleNormGroup L := by
  obtain ⟨φ, hφ, hK, hs, hker⟩ := h.exists_artin L
  exact ⟨φ, ⟨hφ, hK, hs, hker⟩, fun ψ hψ => idelicArtin_unique L ψ φ hψ.1 hφ hψ.2.1 hK⟩

/-- **Exercise 5.11** (named statement; Milne, *CFT*, V, Exercise 5.11, p. 182): for a number field $K$, the idèle class
group has subgroups of finite index that are not open. -/
@[kb "milne2020cft" "Ch. V, Exercise 5.11 (input)"]
structure Exercise5_11 (K : Type) [Field K] [NumberField K] : Prop where
  exists_subgroup : ∃ N : Subgroup (IdeleClassGroup (𝓞 K) K), N.FiniteIndex ∧
    ¬ IsOpen (N : Set (IdeleClassGroup (𝓞 K) K))

end NumberFieldKB.MilneCFT
