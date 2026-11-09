import NumberFieldKB.MilneCFT.Ch7.KeyCase

/-!
# The index of $p$-th powers of $S$-units (the input `SUnitIndex` of Lemma 9.3)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
proof of Lemma 9.3 (p. 224), which uses the $S$-unit theorem (Milne, *Algebraic Number Theory*, Theorem 5.9,
bib key `milne2020ant`): $U(S)\cong\mu(K)\times\mathbb Z^{s-1}$, $s = |S| + $ the number of infinite places.

* `index_range_pow_eq`: for a finitely generated abelian group $A$ whose torsion subgroup is cyclic of order divisible
  by the prime $p$, $(A : A^p) = p^{r+1}$, $r$ the rank of $A$.
* `fg_sUnit`, `finrank_sUnit`: $U(S)$ is finitely generated of rank $|S| + r_1 + r_2 - 1$ (Dirichlet's unit theorem in
  Mathlib, `NumberField.Units.finrank_eq`, and the exact sequence $1\to\mathcal O_K^\times\to U(S)\to\mathbb Z^S$).
* `isCyclic_torsion_sUnit`, `dvd_card_torsion_sUnit`: the torsion of $U(S)$ is $\mu(K)$, cyclic, of order divisible
  by $p$ when $\zeta_p\in K$.
* `sUnitIndex`: the named input `SUnitIndex` of `Ch7/KeyCase.lean` holds (unconditionally).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

theorem prod_range_nsmul_index {B C : Type*} [AddCommGroup B] [AddCommGroup C] (p : ℕ) :
    (nsmulAddMonoidHom p : B × C →+ B × C).range.index =
      (nsmulAddMonoidHom p : B →+ B).range.index * (nsmulAddMonoidHom p : C →+ C).range.index := by
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨b, c⟩
  simp [AddMonoidHom.mem_range, Prod.ext_iff, AddSubgroup.mem_prod]

theorem index_range_nsmul_eq {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {p : ℕ}
    (hcyc : IsAddCyclic (AddCommGroup.torsion M))
    (hdvd : p ∣ Nat.card (AddCommGroup.torsion M)) :
    (nsmulAddMonoidHom p : M →+ M).range.index = p ^ (Module.finrank ℤ M + 1) := by
  classical
  set T := Submodule.torsion ℤ M with hT
  obtain ⟨f, hf⟩ := Module.projective_lifting_property T.mkQ (LinearMap.id) T.mkQ_surjective
  let e : (T × (M ⧸ T)) ≃ₗ[ℤ] M :=
    lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  have h1 : (nsmulAddMonoidHom p : M →+ M).range.index =
      (nsmulAddMonoidHom p : T × (M ⧸ T) →+ _).range.index := by
    rw [← AddSubgroup.index_map_equiv _ e.symm.toAddEquiv, AddEquiv.map_range_nsmulAddMonoidHom]
  rw [h1, prod_range_nsmul_index]
  have h2 : (nsmulAddMonoidHom p : (M ⧸ T) →+ _).range.index = p ^ Module.finrank ℤ M := by
    rw [AddSubgroup.index_range_nsmul]
    congr 1
    exact finrank_quotient_eq_of_le_torsion le_rfl
  have h3 : (nsmulAddMonoidHom p : T →+ _).range.index = p := by
    have hTeq : T.toAddSubgroup = AddCommGroup.torsion M := Submodule.torsion_int
    let e2 : T ≃+ AddCommGroup.torsion M := AddEquiv.addSubgroupCongr hTeq
    have hc : IsAddCyclic T := isAddCyclic_of_surjective e2.symm.toAddMonoidHom e2.symm.surjective
    have hcard : Nat.card T = Nat.card (AddCommGroup.torsion M) := Nat.card_congr e2.toEquiv
    have hfin : Finite T :=
      Module.finite_of_fg_torsion T (Submodule.torsion_isTorsion (R := ℤ) (M := M))
    rw [IsAddCyclic.index_nsmulAddMonoidHom_range]
    exact Nat.gcd_eq_right (hcard ▸ hdvd)
  rw [h2, h3]; ring

/-- $(A : A^p) = p^{r+1}$ for a finitely generated abelian group with cyclic torsion of order divisible by $p$. -/
theorem index_range_pow_eq {A : Type*} [CommGroup A] [Group.FG A] {p : ℕ} (hp : p.Prime)
    (hcyc : IsCyclic (CommGroup.torsion A)) (hdvd : p ∣ Nat.card (CommGroup.torsion A)) :
    (powMonoidHom p : A →* A).range.index = p ^ (Module.finrank ℤ (Additive A) + 1) := by
  have _ := hp
  have hfg : Module.Finite ℤ (Additive A) := by
    rw [Module.Finite.iff_addGroup_fg]
    exact GroupFG.iff_add_fg.mp ‹_›
  let e : Additive (CommGroup.torsion A) ≃+ AddCommGroup.torsion (Additive A) :=
    { toFun := fun x => ⟨Additive.ofMul (x.toMul : A), x.toMul.2⟩
      invFun := fun x => Additive.ofMul ⟨x.1.toMul, x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl }
  have hc : IsAddCyclic (AddCommGroup.torsion (Additive A)) :=
    isAddCyclic_of_surjective e.toAddMonoidHom e.surjective
  have hd : p ∣ Nat.card (AddCommGroup.torsion (Additive A)) := by
    rwa [← Nat.card_congr e.toEquiv, Nat.card_congr (Additive.toMul.trans (Equiv.refl _))]
  have := index_range_nsmul_eq (M := Additive A) hc hd
  rw [← this, ← Subgroup.index_toAddSubgroup]
  rfl

variable (K : Type) [Field K] [NumberField K]

theorem val_eq_one_of_pow {x : K} {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (h : v.valuation K x ^ n = 1) : v.valuation K x = 1 := by
  have := (pow_left_inj₀ (zero_le : 0 ≤ v.valuation K x) zero_le hn).1 (h.trans (one_pow n).symm)
  exact this

theorem val_unit_of_pow_eq_one {x : Kˣ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1)
    (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (x : K) = 1 := by
  apply val_eq_one_of_pow K hn
  rw [← map_pow, ← Units.val_pow_eq_pow_val, h]
  simp

/-- the torsion of `Kˣ` lies in every `S.unit K`. -/
theorem mem_sUnit_of_isOfFinOrder (S : Set (HeightOneSpectrum (𝓞 K))) {x : Kˣ}
    (hx : IsOfFinOrder x) : x ∈ S.unit K := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  intro v _
  exact val_unit_of_pow_eq_one K hn.ne' h v

theorem isOfFinOrder_of_sub {G : Type*} [Group G] (H : Subgroup G) {x : H}
    (hx : IsOfFinOrder (x : G)) : IsOfFinOrder x := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (by simpa using h)⟩

/-- surjection from the torsion of the units of `𝓞 K` onto the torsion of `U(S)`. -/
def torsionHom (S : Set (HeightOneSpectrum (𝓞 K))) :
    NumberField.Units.torsion K →* CommGroup.torsion (S.unit K) where
  toFun x :=
    let hx0 : IsOfFinOrder (x : (𝓞 K)ˣ) := (CommGroup.mem_torsion _).1 x.2
    let hx : IsOfFinOrder (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (x : (𝓞 K)ˣ)) :=
      MonoidHom.isOfFinOrder _ hx0
    let hS := mem_sUnit_of_isOfFinOrder K S hx
    ⟨⟨_, hS⟩, (CommGroup.mem_torsion _).2 (isOfFinOrder_of_sub _ hx)⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp

theorem torsionHom_surjective (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (torsionHom K S) := by
  rintro ⟨⟨y, hyS⟩, hy⟩
  have hy' : IsOfFinOrder (⟨y, hyS⟩ : S.unit K) := (CommGroup.mem_torsion _).1 hy
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.mp hy'
  have hyn : y ^ n = 1 := by simpa using congrArg Subtype.val h
  have hint : IsIntegral ℤ ((y : Kˣ) : K) := by
    apply IsIntegral.of_pow hn
    rw [← Units.val_pow_eq_pow_val, hyn]
    exact isIntegral_one
  let y' : 𝓞 K := ⟨((y : Kˣ) : K), hint⟩
  have hy'n : y' ^ n = 1 := by
    have h1 : ((y : Kˣ) : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hyn]; simp
    apply Subtype.ext
    show (((y : Kˣ) : K)) ^ n = 1
    exact h1
  have hu : IsUnit y' := IsUnit.of_pow_eq_one hy'n hn.ne'
  have hut : hu.unit ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext hy'n⟩
  refine ⟨⟨hu.unit, hut⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

theorem vz_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) = 0 ↔ v.valuation K (x : K) = 1 := by
  rw [toAdd_eq_zero, ← HeightOneSpectrum.valuationOfNeZero_eq]
  norm_cast

theorem val_map_unit (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    v.valuation K ((Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u : Kˣ) : K) = 1 := by
  rw [← vz_eq_zero_iff]
  simp [HeightOneSpectrum.valuation_of_unit_eq]

/-- the valuation vector of an `S`-unit. -/
def sUnitVal (S : Set (HeightOneSpectrum (𝓞 K))) : Additive (S.unit K) →+ (S → ℤ) where
  toFun x := fun v => Multiplicative.toAdd
    (v.1.valuationOfNeZero (((Additive.toMul x : S.unit K)) : Kˣ))
  map_zero' := by ext v; simp
  map_add' x y := by ext v; simp

/-- the inclusion of the units of `𝓞 K` into the `S`-units. -/
def unitsToSUnit (S : Set (HeightOneSpectrum (𝓞 K))) : Additive (𝓞 K)ˣ →+ Additive (S.unit K) where
  toFun x := Additive.ofMul ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (Additive.toMul x),
    fun v _ => val_map_unit K v _⟩
  map_zero' := by apply Additive.toMul.injective; apply Subtype.ext; simp
  map_add' x y := by apply Additive.toMul.injective; apply Subtype.ext; simp

theorem unitsToSUnit_injective (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (unitsToSUnit K S) := by
  intro x y h
  have h1 := congrArg (fun z => ((Additive.toMul z : S.unit K) : Kˣ)) h
  simp only [unitsToSUnit, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul] at h1
  have h2 : Additive.toMul x = Additive.toMul y := by
    apply Units.ext
    have := congrArg (fun z : Kˣ => (z : K)) h1
    exact IsFractionRing.injective (𝓞 K) K (by simpa using this)
  exact Additive.toMul.injective h2

theorem sUnitVal_eq_zero_iff (S : Set (HeightOneSpectrum (𝓞 K))) (x : Additive (S.unit K)) :
    sUnitVal K S x = 0 ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K (((Additive.toMul x : S.unit K) : Kˣ) : K) = 1 := by
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have := congrFun h ⟨v, hv⟩
      exact (vz_eq_zero_iff K v _).1 this
    · exact (Additive.toMul x).2 v hv
  · intro h
    ext v
    exact (vz_eq_zero_iff K v.1 _).2 (h v.1)

theorem ker_sUnitVal_le (S : Set (HeightOneSpectrum (𝓞 K))) (x : Additive (S.unit K))
    (hx : sUnitVal K S x = 0) : ∃ u, unitsToSUnit K S u = x := by
  have h := (sUnitVal_eq_zero_iff K S x).1 hx
  set y : Kˣ := ((Additive.toMul x : S.unit K) : Kˣ) with hy
  have hint : ∀ z : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (z : K) ≤ 1) →
      ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = z := by
    intro z hz
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one K (z : K) hz
  obtain ⟨a, ha⟩ := hint y (fun v => (h v).le)
  obtain ⟨b, hb⟩ := hint y⁻¹ (fun v => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, h v]; simp)
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, ha, hb, map_one]
    simp
  refine ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp [unitsToSUnit, ha]
  rfl

theorem exists_sUnit_pole (S : Set (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∈ S) : ∃ x : S.unit K,
      (∀ u : HeightOneSpectrum (𝓞 K), u ≠ w → u.valuation K ((x : Kˣ) : K) = 1) ∧
        w.valuation K ((x : Kˣ) : K) ≠ 1 := by
  classical
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprinc : (w.asIdeal ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩ :
        nonZeroDivisors (Ideal (𝓞 K))) ^ h = 1 := pow_card_eq_one
    rw [← map_pow, ClassGroup.mk0_eq_one_iff] at h1
    exact h1
  obtain ⟨a, ha⟩ := hprinc
  have ha' : w.asIdeal ^ h = Ideal.span {a} := by rw [ha]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : w.asIdeal ^ h = ⊥ := by rw [ha']; simp
    exact pow_ne_zero h w.ne_bot this
  have hmem : a ∈ w.asIdeal := by
    have : a ∈ w.asIdeal ^ h := by rw [ha']; exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hpos.ne' this
  have hnot : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ w → a ∉ u.asIdeal := by
    intro u huw hau
    have h1 : w.asIdeal ^ h ≤ u.asIdeal := by
      rw [ha', Ideal.span_singleton_le_iff_mem]; exact hau
    have h2 : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le h1
    have h3 : w.asIdeal = u.asIdeal := w.isMaximal.eq_of_le u.isPrime.ne_top h2
    exact huw (HeightOneSpectrum.ext h3.symm)
  have hne : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha0
  let y : Kˣ := Units.mk0 _ hne
  have hy : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ w → u.valuation K (y : K) = 1 := by
    intro u huw
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) u).2 (hnot u huw)
  refine ⟨⟨y, fun u hu => hy u ?_⟩, hy, ?_⟩
  · rintro rfl; exact hu hw
  · show w.valuation K (algebraMap (𝓞 K) K a) ≠ 1
    exact ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w a).2 hmem).ne

theorem finrank_range_sUnitVal (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    S.ncard ≤ Module.finrank ℤ (LinearMap.range (sUnitVal K S).toIntLinearMap) := by
  classical
  have : Fintype S := hS.fintype
  choose! x hx1 hx2 using exists_sUnit_pole K S
  let f : S → LinearMap.range (sUnitVal K S).toIntLinearMap := fun w =>
    ⟨(sUnitVal K S).toIntLinearMap (Additive.ofMul (x w.1)), LinearMap.mem_range_self _ _⟩
  have hf : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp (LinearMap.range (sUnitVal K S).toIntLinearMap).subtype
    rw [linearIndependent_iff']
    intro s g hg w hw
    have h1 := congrFun hg w
    rw [Finset.sum_apply, Finset.sum_eq_single w] at h1
    · have hne : (sUnitVal K S (Additive.ofMul (x w.1))) w ≠ 0 := by
        intro h0
        exact hx2 w.1 w.2 ((vz_eq_zero_iff K w.1 _).1 h0)
      simp only [Function.comp_apply, Submodule.subtype_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at h1
      have : g w * (sUnitVal K S (Additive.ofMul (x w.1))) w = 0 := h1
      exact (mul_eq_zero.1 this).resolve_right hne
    · intro u _ huw
      have : (sUnitVal K S (Additive.ofMul (x u.1))) w = 0 := by
        apply (vz_eq_zero_iff K w.1 _).2
        exact hx1 u.1 u.2 w.1 (fun h => huw (Subtype.ext h.symm))
      show g u • (sUnitVal K S (Additive.ofMul (x u.1))) w = 0
      rw [this, smul_zero]
    · intro h; exact absurd hw h
  have := hf.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at this
  exact this

/-- $U(S)$ is finitely generated for $S$ finite. -/
theorem fg_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : Group.FG (S.unit K) := by
  have : Finite S := hS.to_subtype
  let φ := (sUnitVal K S).toIntLinearMap
  let ι := (unitsToSUnit K S).toIntLinearMap
  have hker : LinearMap.ker φ = LinearMap.range ι := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx; exact ker_sUnitVal_le K S x hx
    · rintro ⟨u, rfl⟩
      show sUnitVal K S (unitsToSUnit K S u) = 0
      rw [sUnitVal_eq_zero_iff]
      intro v
      exact val_map_unit K v _
  have hfin : Module.Finite ℤ (Additive (S.unit K)) := by
    constructor
    apply Submodule.fg_of_fg_map_of_fg_inf_ker φ
    · rw [Submodule.map_top]
      exact (Module.Finite.iff_fg.1 inferInstance : (LinearMap.range φ).FG)
    · rw [top_inf_eq, hker]
      exact (Module.Finite.iff_fg.1 inferInstance : (LinearMap.range ι).FG)
  rw [Module.Finite.iff_addGroup_fg] at hfin
  exact GroupFG.iff_add_fg.mpr hfin

/-- The $\mathbb Z$-rank of $U(S)$ is $|S| + r_1 + r_2 - 1$. -/
theorem finrank_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Module.finrank ℤ (Additive (S.unit K)) = S.ncard + NumberField.Units.rank K := by
  have : Finite S := hS.to_subtype
  have : Fintype S := hS.fintype
  have hfg := fg_sUnit K S hS
  have : Module.Finite ℤ (Additive (S.unit K)) := by
    rw [Module.Finite.iff_addGroup_fg]
    exact GroupFG.iff_add_fg.mp hfg
  let φ := (sUnitVal K S).toIntLinearMap
  let ι := (unitsToSUnit K S).toIntLinearMap
  have hker : LinearMap.ker φ = LinearMap.range ι := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx; exact ker_sUnitVal_le K S x hx
    · rintro ⟨u, rfl⟩
      show sUnitVal K S (unitsToSUnit K S u) = 0
      rw [sUnitVal_eq_zero_iff]
      intro v
      exact val_map_unit K v _
  have hι : Function.Injective ι := unitsToSUnit_injective K S
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, LinearMap.finrank_range_of_inj hι, NumberField.Units.finrank_eq] at h1
  have h2 : Module.finrank ℤ (LinearMap.range φ) ≤ S.ncard := by
    calc Module.finrank ℤ (LinearMap.range φ) ≤ Module.finrank ℤ (S → ℤ) := Submodule.finrank_le _
      _ = S.ncard := by
        rw [Module.finrank_pi, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h3 : S.ncard ≤ Module.finrank ℤ (LinearMap.range φ) := finrank_range_sUnitVal K S hS
  omega

/-- The torsion subgroup of $U(S)$ (the roots of unity of $K$) is cyclic. -/
theorem isCyclic_torsion_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsCyclic (CommGroup.torsion (S.unit K)) :=
  isCyclic_of_surjective _ (torsionHom_surjective K S)

/-- If $\zeta_p\in K$, $p$ divides the order of the torsion of $U(S)$. -/
theorem dvd_card_torsion_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p) : p ∣ Nat.card (CommGroup.torsion (S.unit K)) := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hu : IsUnit ζ := hζ.isUnit hp.ne_zero
  let u : Kˣ := hu.unit
  have hup : u ^ p = 1 := Units.ext (by simpa [u] using hζ.pow_eq_one)
  have hmem : u ∈ S.unit K := mem_sUnit_of_isOfFinOrder K S
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hup⟩)
  have hord : orderOf u = p := by
    rw [← orderOf_units]
    exact hζ.eq_orderOf.symm
  let t : CommGroup.torsion (S.unit K) := ⟨⟨u, hmem⟩, (CommGroup.mem_torsion _).2
    (isOfFinOrder_of_sub _ (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hup⟩))⟩
  have : orderOf t = p := by
    rw [← hord, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  rw [← this]
  exact orderOf_dvd_natCard t

/-- **The index of $p$-th powers of $S$-units** (Milne, *CFT*, Chapter VII, proof of Lemma 9.3, from the $S$-unit
theorem): the named statement `SUnitIndex` holds for every number field. -/
@[kb "milne2020cft" "Ch. VII, proof of Lemma 9.3 (S-unit index, proved)"]
theorem sUnitIndex : SUnitIndex K := by
  refine ⟨fun p S hp hζ hS => ?_⟩
  have := fg_sUnit K S hS
  have key := index_range_pow_eq (A := S.unit K) hp (isCyclic_torsion_sUnit K S)
    (dvd_card_torsion_sUnit K S hp hζ)
  rw [finrank_sUnit K S hS] at key
  have hrel : (powMonoidHom p : Kˣ →* Kˣ).range.relIndex (S.unit K) =
      (powMonoidHom p : S.unit K →* S.unit K).range.index := by
    unfold Subgroup.relIndex
    congr 1
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨x, hx⟩
      have hxS : x ∈ S.unit K := by
        intro v hv
        apply val_eq_one_of_pow K hp.ne_zero v
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hx]
        exact hy v hv
      exact ⟨⟨x, hxS⟩, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  rw [hrel, key]
  have hc : Fintype.card (InfinitePlace K) = NumberField.Units.rank K + 1 := by
    have := Fintype.card_pos (α := InfinitePlace K)
    unfold NumberField.Units.rank
    omega
  rw [hc]
  congr 1

end NumberFieldKB.MilneCFT.Ch7
