import NumberFieldKB.MilneCFT.Ch7.Reciprocity
import NumberFieldKB.MilneCFT.Ch7.IdeleOpen
import NumberFieldKB.MilneCFT.Ch8.Theorem23Uncond
import NumberFieldKB.MilneCFT.Ch5ConductorUncond
import NumberFieldKB.Chebotarev.Cyclotomic
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# Milne, *Class Field Theory*, VII Theorem 8.1 (a) and Example 8.2, unconditional

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, §8, p. 221.

`Theorem8_1a K Ω` quantifies over every family `ψ` of homomorphisms `𝕀_K → Gal(E/K)` ($E$ finite abelian in
$\Omega$) with the properties `IsGlobalArtinMap` (open kernels, trivial on norms, Frobenius at unramified primes,
compatible with restriction, local images the decomposition groups). We prove that every such family **equals**
Tau Ceti's idèlic Artin map `idelicArtinTauCeti` (`T81.eq_idelicArtinTauCeti`), which is trivial on $K^\times$ by
global reciprocity; Theorem 8.1 (a) (`theorem8_1a`) and Example 8.2 (`example8_2`) follow.

**The uniqueness argument.** Write $\phi_E$ for Tau Ceti's map.
1. (`mem_zpowers_of_local`) For an idèle $y$ concentrated at one place, $\psi_E(y) \in \langle\phi_E(y)\rangle$:
   let $F \subseteq E$ be the fixed field of $\langle\phi_E(y)\rangle$ (`exists_abExt_of_subgroup`); then
   $\phi_F(y) = 1$ (`tc_compat`), so $y$ is a norm from $F$ by local–global compatibility of norm groups
   (`mem_normIdeles_of_tc_finite`, `mem_normIdeles_of_tc_infinite`, from `Ch8.T23`), so $\psi_F(y) = 1$, i.e.
   $\psi_E(y)$ fixes $F$.
2. (`eq_tc_of_uniformizer`) At a prime element $x$ of $K_v$: with $q = Nv$, $N = [E:K]$, $m = q^N - 1$ and
   $E'' = E(\zeta_m)$, step 1 gives $\psi_{E''}(x) = \phi_{E''}(x)^k$. On $K(\zeta_m)$, unramified at $v$, both
   are the Frobenius, which acts on $\zeta_m$ by $\zeta\mapsto\zeta^q$ (`autToPow_frobAt`); $q$ has order $N$ modulo
   $m$ (`orderOf_unit_eq`), so $N \mid k-1$, and on $E$ we get $\psi_E(x) = \phi_E(x)^k = \phi_E(x)$.
3. (`eq_tc_finite`, `eq_tc_infinite`) Hence agreement on all of $K_v^\times$; at an infinite place both maps take
   values in the decomposition group, of order $\le 2$, and step 1 suffices (`hom_eq_of_card_le_two`).
4. (`ideleHom_eq_of_local_open`) Homomorphisms with open kernels agreeing on every $K_v^\times$ are equal.

This settles the question whether the properties of `IsGlobalArtinMap` force
triviality on $K^\times$: they do.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch7
namespace T81

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

instance isAbelianGalois (E : AbExt K Ω) : IsAbelianGalois K E.L :=
  { toIsGalois := E.isGalois, toIsMulCommutative := ⟨⟨E.comm⟩⟩ }

/-- Tau Ceti's Artin maps are compatible with restriction. -/
theorem tc_compat {E E' : AbExt K Ω} (h : E'.L ≤ E.L) (x : IdeleGroup (𝓞 K) K) :
    galRestrict h (idelicArtinTauCeti E.L x) = idelicArtinTauCeti E'.L x := by
  apply Abelianization.of_injective
  have h1 := TauCeti.ClassFieldTheory.globalArtinMap_comp K E.L (IntermediateField.inclusion h)
    IsSepClosed.lift
  have h2 := congrArg (fun F => F (Additive.ofMul (x : IdeleClassGroup (𝓞 K) K))) h1
  simp only [AddMonoidHom.comp_apply] at h2
  conv_rhs => rw [idelicArtinTauCeti_apply, TauCeti.ClassFieldTheory.of_ideleClassArtinMap K E'.L
    (IsSepClosed.lift.comp (IntermediateField.inclusion h)), ← h2]
  rw [← Abelianization.map_of, of_idelicArtinTauCeti]
  rfl

theorem galRestrict_eq {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] :
    galRestrict h = (IntermediateField.inclusion h).restrictNormalHom := rfl

theorem galRestrict_apply {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] (σ : Gal(L'/K)) (y : L) :
    ((galRestrict h σ y : L) : Ω) = (σ (IntermediateField.inclusion h y) : Ω) := by
  rw [galRestrict_eq]
  exact congrArg Subtype.val ((IntermediateField.inclusion h).restrictNormalHom_commutes σ y)

theorem galRestrict_surjective {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] [Normal K L'] :
    Function.Surjective (galRestrict h) := by
  rw [galRestrict_eq]
  exact (IntermediateField.inclusion h).restrictNormalHom_surjective

/-- Every Galois subextension of a finite abelian extension, as an `AbExt`. -/
def AbExt.ofLE (E : AbExt K Ω) (F : IntermediateField K Ω) (h : F ≤ E.L) [IsGalois K F] : AbExt K Ω where
  L := F
  finiteDimensional := .of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).toRingHom.injective
  isGalois := inferInstance
  comm σ τ := by
    obtain ⟨σ', rfl⟩ := galRestrict_surjective h σ
    obtain ⟨τ', rfl⟩ := galRestrict_surjective h τ
    rw [← map_mul, ← map_mul, E.comm]

/-- **Galois correspondence inside an abelian extension**: for a subgroup `H` of `Gal(E/K)` there is a finite
abelian `F ⊆ E` with `ker(Gal(E/K) → Gal(F/K)) = H`. -/
theorem exists_abExt_of_subgroup (E : AbExt K Ω) (H : Subgroup Gal(E.L/K)) :
    ∃ (F : AbExt K Ω) (h : F.L ≤ E.L), ∀ σ, galRestrict h σ = 1 ↔ σ ∈ H := by
  classical
  have : H.Normal := ⟨fun n hn g => by rw [E.comm g n, mul_inv_cancel_right]; exact hn⟩
  let F0 : IntermediateField K E.L := IntermediateField.fixedField H
  let F : IntermediateField K Ω := F0.map E.L.val
  have hle : F ≤ E.L := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have : IsGalois K F := IsGalois.of_algEquiv (IntermediateField.equivMap F0 E.L.val)
  have key : ∀ σ, galRestrict hle σ = 1 ↔ σ ∈ H := by
    intro σ
    rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h1 z hz
      have h2 := congrArg (fun τ : Gal(F/K) => (τ ⟨(z : Ω), ⟨z, hz, rfl⟩⟩ : Ω)) h1
      apply Subtype.ext
      rw [galRestrict_apply] at h2
      exact h2
    · intro h1
      ext ⟨y, hy⟩
      obtain ⟨z, hz, rfl⟩ := hy
      rw [galRestrict_apply]
      exact congrArg Subtype.val (h1 z hz)
  exact ⟨AbExt.ofLE E F hle, hle, key⟩

/-- The compositum of two finite abelian extensions. -/
def AbExt.sup (E M : AbExt K Ω) : AbExt K Ω where
  L := E.L ⊔ M.L
  finiteDimensional := inferInstance
  isGalois := inferInstance
  comm σ τ := by
    apply IntermediateField.restrictNormalHomSupProd_injective E.L M.L
    rw [map_mul, map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, E.comm, M.comm]

/-- **Local–global norms at a finite place**: if Tau Ceti's Artin symbol of the idele concentrated at `v` is
trivial, that idele is a norm. -/
theorem mem_normIdeles_of_tc_finite (F : AbExt K Ω) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (h : idelicArtinTauCeti F.L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = 1) :
    IdeleGroup.ofAdicCompletion (𝓞 K) K v x ∈ normIdeles K F.L := by
  have h1 : (IdeleGroup.ofAdicCompletion (𝓞 K) K v x : IdeleClassGroup (𝓞 K) K) ∈ normClasses K F.L := by
    rw [normClasses_eq_tauCeti, ← TauCeti.ClassFieldTheory.ker_ideleClassArtinMap]
    exact h
  exact (Ch8.T23.mem_normClasses_finite_iff F.L v x).1 h1

/-- **Local–global norms at an infinite place.** -/
theorem mem_normIdeles_of_tc_infinite (F : AbExt K Ω) (w : InfinitePlace K)
    (x : w.Completionˣ) (h : idelicArtinTauCeti F.L (IdeleGroup.ofCompletion (𝓞 K) K w x) = 1) :
    IdeleGroup.ofCompletion (𝓞 K) K w x ∈ normIdeles K F.L := by
  have h1 : (IdeleGroup.ofCompletion (𝓞 K) K w x : IdeleClassGroup (𝓞 K) K) ∈ normClasses K F.L := by
    rw [normClasses_eq_tauCeti, ← TauCeti.ClassFieldTheory.ker_ideleClassArtinMap]
    exact h
  exact (Ch8.T23.mem_normClasses_infinite_iff F.L w x).1 h1

/-- The cyclotomic extension `K(ζ)` inside `Ω`, `ζ` a primitive `m`-th root of unity, as an `AbExt`. -/
def cycExt {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) : AbExt K Ω :=
  haveI : IsCyclotomicExtension {m} K (IntermediateField.adjoin K {ζ}) := hζ.intermediateField_adjoin_isCyclotomicExtension K
  { L := (IntermediateField.adjoin K {ζ})
    finiteDimensional := IsCyclotomicExtension.finiteDimensional {m} K (IntermediateField.adjoin K {ζ})
    isGalois := IsCyclotomicExtension.isGalois {m} K (IntermediateField.adjoin K {ζ})
    comm := fun σ τ => by
      have hζ' := IsCyclotomicExtension.zeta_spec m K (IntermediateField.adjoin K {ζ})
      apply hζ'.autToPow_injective K
      rw [map_mul, map_mul, mul_comm] }

instance cycExt_isCyclotomic {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (cycExt (K := K) hζ).L :=
  hζ.intermediateField_adjoin_isCyclotomicExtension K

/-- `q` has order exactly `N` modulo `q^N - 1`. -/
theorem orderOf_unit_eq {q N : ℕ} (hq : 2 ≤ q) (hN : 0 < N) (u : (ZMod (q ^ N - 1))ˣ)
    (hu : (u : ZMod (q ^ N - 1)) = q) : orderOf u = N := by
  have hqN : 1 ≤ q ^ N := Nat.one_le_pow _ _ (by omega)
  rw [orderOf_eq_iff hN]
  constructor
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_one]
    have h1 : q ^ N = (q ^ N - 1) + 1 := (Nat.sub_add_cancel hqN).symm
    have : ((q ^ N : ℕ) : ZMod (q ^ N - 1)) = 1 := by
      rw [h1, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    exact_mod_cast this
  · intro j hjN hj0 h
    have h2 : ((q ^ j : ℕ) : ZMod (q ^ N - 1)) = ((1 : ℕ) : ZMod (q ^ N - 1)) := by
      have := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hu, Units.val_one] at this
      exact_mod_cast this
    rw [ZMod.natCast_eq_natCast_iff] at h2
    have h5 : 2 ≤ q ^ j := le_trans hq (Nat.le_self_pow (by omega) q)
    have h3 : (q ^ N - 1) ∣ q ^ j - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h2.symm
    have h4 : q ^ j < q ^ N := Nat.pow_lt_pow_right (by omega) hjN
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem coprime_pow_sub_one {q N : ℕ} (hq : 1 ≤ q) (hN : 0 < N) : q.Coprime (q ^ N - 1) := by
  have hqN : 1 ≤ q ^ N := Nat.one_le_pow _ _ (by omega)
  have h : (q ^ N).Coprime (q ^ N - 1) := by
    have := (Nat.coprime_self_add_left (m := q ^ N - 1) (n := 1)).2 (Nat.coprime_one_left _)
    rwa [Nat.sub_add_cancel hqN] at this
  exact h.coprime_dvd_left (dvd_pow_self q hN.ne')

/-- Two homomorphisms into a subgroup `S` of order at most `2`, the second onto `S`, with `f₂(a)` always a power
of `f₁(a)`, are equal. -/
theorem hom_eq_of_card_le_two {A G : Type*} [Group A] [Group G] (f₁ f₂ : A →* G) (S : Subgroup G)
    (hS : Nat.card S = 1 ∨ Nat.card S = 2) (h₁ : ∀ a, f₁ a ∈ S) (h₂ : f₂.range = S)
    (hz : ∀ a, f₂ a ∈ Subgroup.zpowers (f₁ a)) : f₁ = f₂ := by
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hsq : ∀ c ∈ S, c ^ 2 = 1 := by
    intro c hc
    have h := orderOf_dvd_natCard (⟨c, hc⟩ : S)
    have h2 : orderOf (⟨c, hc⟩ : S) ∣ 2 := by
      rcases hS with h' | h' <;> rw [h'] at h
      · exact h.trans (one_dvd 2)
      · exact h
    have := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h2)
    simpa using this
  have huniq : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ 1 → c₂ ≠ 1 → c₁ = c₂ := by
    intro c₁ h1 c₂ h2 hc1 hc2
    by_contra hne
    let f : Fin 3 → S := ![1, ⟨c₁, h1⟩, ⟨c₂, h2⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
    have := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have hpow : ∀ c ∈ S, ∀ k : ℤ, c ^ k = 1 ∨ c ^ k = c := by
    intro c hc k
    rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, ← pow_two, hsq c hc, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, ← pow_two, hsq c hc, one_zpow, one_mul]
  have hone : ∀ a, f₁ a = 1 → f₂ a = 1 := by
    intro a ha
    have := hz a
    rw [ha, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact this
  ext a
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz a)
  rcases hpow (f₁ a) (h₁ a) k with h | h
  · rw [h] at hk
    by_contra hne
    have ha1 : f₁ a ≠ 1 := fun h' => hne (by rw [← hk, h'])
    obtain ⟨b, hb⟩ : f₁ a ∈ f₂.range := by rw [h₂]; exact h₁ a
    have hb1 : f₁ b ≠ 1 := fun h' => ha1 (by rw [← hb, hone b h'])
    have hab : f₁ a = f₁ b := huniq _ (h₁ a) _ (h₁ b) ha1 hb1
    have h3 : f₁ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h4 := hone _ h3
    rw [map_mul, map_inv, ← hk, one_mul, inv_eq_one, hb] at h4
    exact ha1 h4
  · rw [h] at hk
    exact hk

theorem ideleFinAt_ne_zero (y : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : ideleFinAt y v ≠ 0 := by
  have h3 : ideleFinAt y v * ideleFinAt y⁻¹ v = 1 :=
    congrArg (fun a : IdeleGroup (𝓞 K) K => ideleFinAt a v) (mul_inv_cancel y)
  exact left_ne_zero_of_mul_eq_one h3

theorem ideleInfAt_ne_zero (y : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) : ideleInfAt y w ≠ 0 := by
  have h3 : ideleInfAt y w * ideleInfAt y⁻¹ w = 1 :=
    congrArg (fun a : IdeleGroup (𝓞 K) K => ideleInfAt a w) (mul_inv_cancel y)
  exact left_ne_zero_of_mul_eq_one h3

/-- **Homomorphisms on ideles agreeing locally**: two homomorphisms with open kernels that agree on every
`K_v^×` and every `K_w^×` are equal (an idele is a finite product of local components times an idele in any
given open subgroup). -/
theorem ideleHom_eq_of_local_open {G : Type*} [Group G] (f g : IdeleGroup (𝓞 K) K →* G)
    (hopen : IsOpen ((f.ker ⊓ g.ker : Subgroup _) : Set (IdeleGroup (𝓞 K) K)))
    (hfin : ∀ v z, f (IdeleGroup.ofAdicCompletion (𝓞 K) K v z) = g (IdeleGroup.ofAdicCompletion (𝓞 K) K v z))
    (hinf : ∀ w z, f (IdeleGroup.ofCompletion (𝓞 K) K w z) = g (IdeleGroup.ofCompletion (𝓞 K) K w z)) :
    f = g := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_of_isOpen _ hopen
  -- clearing finitely many finite components
  have keyF : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ y : IdeleGroup (𝓞 K) K,
      (∀ w, ideleInfAt y w = 1) →
      (∀ v ∉ T, (v ∈ S₀ → ideleFinAt y v = 1) ∧ Valued.v (ideleFinAt y v) = 1) → f y = g y := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro y h1 h2
      have hy := hS₀ y h1 (fun v hv => (h2 v (Finset.notMem_empty v)).1 hv)
        (fun v => (h2 v (Finset.notMem_empty v)).2)
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hy
      rw [hy.1, hy.2]
    | insert v T hvT ih =>
      intro y h1 h2
      let u : (v.adicCompletion K)ˣ := Units.mk0 _ (ideleFinAt_ne_zero y v)
      set z := IdeleGroup.ofAdicCompletion (𝓞 K) K v u⁻¹ with hz
      have hyz : f (y * z) = g (y * z) := by
        refine ih (y * z) (fun w => ?_) (fun v' hv' => ?_)
        · rw [ideleInfAt_mul, h1 w, ideleInfAt_ofAdic, mul_one]
        · by_cases hvv : v' = v
          · subst hvv
            have : ideleFinAt (y * z) v' = 1 := by
              rw [ideleFinAt_mul, hz, ideleFinAt_ofAdic_self]
              simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0]
              exact mul_inv_cancel₀ (ideleFinAt_ne_zero y _)
            rw [this, map_one]
            exact ⟨fun _ => rfl, rfl⟩
          · rw [ideleFinAt_mul, hz, ideleFinAt_ofAdic_ne hvv, mul_one]
            exact h2 v' (by simp [hvv, hv'])
      have hzz : f z = g z := hfin v _
      have e : y = (y * z) * z⁻¹ := (mul_inv_cancel_right y z).symm
      rw [e, f.map_mul, g.map_mul, f.map_inv, g.map_inv, hyz, hzz]
  -- clearing the infinite components
  have keyI : ∀ U : Finset (InfinitePlace K), ∀ y : IdeleGroup (𝓞 K) K,
      (∀ w ∉ U, ideleInfAt y w = 1) →
      (∀ v ∉ (S₀ ∪ (finite_valued_ne_one y).toFinset), (v ∈ S₀ → ideleFinAt y v = 1) ∧
        Valued.v (ideleFinAt y v) = 1) → f y = g y := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro y h1 h2
      exact keyF _ y (fun w => h1 w (Finset.notMem_empty w)) h2
    | insert w U hwU ih =>
      intro y h1 h2
      let u : w.Completionˣ := Units.mk0 _ (ideleInfAt_ne_zero y w)
      set z := IdeleGroup.ofCompletion (𝓞 K) K w u⁻¹ with hz
      have hfz : ∀ v, ideleFinAt (y * z) v = ideleFinAt y v := fun v => by
        rw [ideleFinAt_mul, hz, ideleFinAt_ofCompletion, mul_one]
      have hset : (finite_valued_ne_one (y * z)).toFinset = (finite_valued_ne_one y).toFinset := by
        ext v
        simp [hfz]
      have hyz : f (y * z) = g (y * z) := by
        refine ih (y * z) (fun w' hw' => ?_) (fun v hv => ?_)
        · by_cases hww : w' = w
          · subst hww
            rw [ideleInfAt_mul, hz, ideleInfAt_ofCompletion_self]
            simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0]
            exact mul_inv_cancel₀ (ideleInfAt_ne_zero y _)
          · rw [ideleInfAt_mul, hz, ideleInfAt_ofCompletion_ne w w' hww, mul_one]
            exact h1 w' (by simp [hww, hw'])
        · rw [hset] at hv
          rw [hfz]
          exact h2 v hv
      have hzz : f z = g z := hinf w _
      have e : y = (y * z) * z⁻¹ := (mul_inv_cancel_right y z).symm
      rw [e, f.map_mul, g.map_mul, f.map_inv, g.map_inv, hyz, hzz]
  ext x
  refine keyI Finset.univ x (fun w hw => absurd (Finset.mem_univ w) hw) (fun v hv => ?_)
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨fun h => absurd h hv.1, hv.2⟩

variable (ψ : ArtinFamily K Ω) (hψ : IsGlobalArtinMap K Ω ψ)
include hψ

/-- **The key constraint**: if every subextension `F` whose Tau Ceti Artin symbol of `y` is trivial has `y` among
its norms, then `ψ_E(y)` is a power of Tau Ceti's `φ_E(y)` (apply the hypothesis to the fixed field of
`⟨φ_E(y)⟩`). -/
theorem mem_zpowers_of_local (E : AbExt K Ω) (y : IdeleGroup (𝓞 K) K)
    (hy : ∀ F : AbExt K Ω, idelicArtinTauCeti F.L y = 1 → y ∈ normIdeles K F.L) :
    ψ E y ∈ Subgroup.zpowers (idelicArtinTauCeti E.L y) := by
  obtain ⟨F, hFE, hF⟩ := exists_abExt_of_subgroup E (Subgroup.zpowers (idelicArtinTauCeti E.L y))
  rw [← hF, hψ.compat E F hFE y]
  refine hψ.norm_le_ker F (hy F ?_)
  rw [← tc_compat hFE, hF]
  exact Subgroup.mem_zpowers _

/-- **Agreement at a prime element**: `ψ_E` and Tau Ceti's Artin map agree on the idele concentrated at a finite
prime `v` with component a prime element of `K_v`. Proof: with `q = Nv`, `N = [E:K]`, `m = q^N - 1` and
`E'' = E(ζ_m)`, `ψ_{E''}(x) = φ_{E''}(x)^k` (`mem_zpowers_of_local`); on `K(ζ_m)`, where `v` is unramified, both
are the Frobenius, which acts on `ζ_m` as `ζ ↦ ζ^q`, so `q^k ≡ q` mod `m` and `N ∣ k - 1`; on `E`, `φ_E(x)^N = 1`. -/
theorem eq_tc_of_uniformizer (E : AbExt K Ω) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (hx : Valued.v (x : v.adicCompletion K) = WithZero.exp (-1)) :
    ψ E (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) =
      idelicArtinTauCeti E.L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) := by
  classical
  set y := IdeleGroup.ofAdicCompletion (𝓞 K) K v x with hy
  have hord : ordAt v x = 1 := by simp [ordAt, hx]
  -- the numbers q, N, m
  set q := Ideal.absNorm v.asIdeal with hq
  have hq2 : 2 ≤ q := by
    have := v.isMaximal
    obtain ⟨p, n, hn, -, hp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
    rw [hq, hN]
    exact le_trans hp.two_le (Nat.le_self_pow hn.ne' p)
  set N := Nat.card Gal(E.L/K) with hNdef
  have hN : 0 < N := Nat.card_pos
  set m := q ^ N - 1 with hm
  have hm0 : 0 < m := by
    have : q ≤ q ^ N := Nat.le_self_pow hN.ne' q
    omega
  have : NeZero m := ⟨hm0.ne'⟩
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω m
  let M := cycExt (K := K) hζ
  let E2 := AbExt.sup E M
  have hE : E.L ≤ E2.L := le_sup_left
  have hM : M.L ≤ E2.L := le_sup_right
  -- the constraint in E''
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_local ψ hψ E2 y fun F h => mem_normIdeles_of_tc_finite F v x h)
  -- restriction to K(ζ_m)
  have hcop : q.Coprime m := coprime_pow_sub_one (by omega) hN
  have hvM : v ∈ unramifiedPrimes K M.L := fun Q _ _ =>
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem M.L m (natCast_notMem_of_coprime hcop) Q
  obtain ⟨Q⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M.L)))
  have hψM : ψ M y = frobAt K M.L v Q := by rw [hψ.unramified M v hvM Q x, hord, zpow_one]
  have hφM : idelicArtinTauCeti M.L y = frobAt K M.L v Q := by
    rw [idelicArtinTauCeti_frobenius M.L v hvM x hx, artinFrob_eq M.L v hvM Q]
  have h1 : frobAt K M.L v Q ^ k = frobAt K M.L v Q := by
    have := congrArg (galRestrict hM) hk
    rwa [map_zpow, tc_compat hM, hψ.compat E2 M hM, hφM, hψM] at this
  have hζM := IsCyclotomicExtension.zeta_spec m K M.L
  have hσ := autToPow_frobAt K m hcop Q
  set u := hζM.autToPow K (frobAt K M.L v Q) with hu
  have hu1 : u ^ k = u := by rw [hu, ← map_zpow, h1]
  have hu2 : u ^ (k - 1) = 1 := by rw [zpow_sub_one, hu1, mul_inv_cancel]
  have huo : orderOf u = N := orderOf_unit_eq hq2 hN u (by rw [hu, hσ])
  have hdvd : (N : ℤ) ∣ k - 1 := by rw [← huo]; exact orderOf_dvd_iff_zpow_eq_one.2 hu2
  -- restriction to E
  have h2 := congrArg (galRestrict hE) hk
  rw [map_zpow, tc_compat hE, hψ.compat E2 E hE] at h2
  rw [← h2]
  obtain ⟨j, hj⟩ := hdvd
  have hk' : k = 1 + (N : ℤ) * j := by omega
  rw [hk', zpow_add, zpow_one, zpow_mul, zpow_natCast, hNdef, pow_card_eq_one', one_zpow, mul_one]

/-- **Agreement at every finite place.** A unit of `K_v` is a quotient of two prime elements. -/
theorem eq_tc_finite (E : AbExt K Ω) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ψ E (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) =
      idelicArtinTauCeti E.L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) := by
  obtain ⟨π, hπ⟩ := exists_unit_uniformizer v
  have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  set a : ℤ := WithZero.log (Valued.v (x : v.adicCompletion K)) with ha
  have hxv : Valued.v (x : v.adicCompletion K) = WithZero.exp a := (WithZero.exp_log hx0).symm
  have hy : Valued.v ((x * π ^ (a + 1) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1) := by
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hxv, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    congr 1
    simp only [smul_eq_mul]
    ring
  have e1 := eq_tc_of_uniformizer ψ hψ E v _ hy
  have e2 := eq_tc_of_uniformizer ψ hψ E v π hπ
  have hxe : IdeleGroup.ofAdicCompletion (𝓞 K) K v x =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v (x * π ^ (a + 1)) *
        (IdeleGroup.ofAdicCompletion (𝓞 K) K v π) ^ (-(a + 1)) := by
    rw [← map_zpow, ← map_mul]
    congr 1
    group
  rw [hxe, (ψ E).map_mul, (idelicArtinTauCeti E.L).map_mul, (ψ E).map_zpow,
    (idelicArtinTauCeti E.L).map_zpow, e1, e2]

/-- **Agreement at every infinite place**: both maps land in the decomposition group `D_w` (order `≤ 2`), `ψ` onto
it, and `ψ_E(z)` is a power of `φ_E(z)` (`mem_zpowers_of_local`), so `hom_eq_of_card_le_two` applies. -/
theorem eq_tc_infinite (E : AbExt K Ω) (w : InfinitePlace K) (z : w.Completionˣ) :
    ψ E (IdeleGroup.ofCompletion (𝓞 K) K w z) =
      idelicArtinTauCeti E.L (IdeleGroup.ofCompletion (𝓞 K) K w z) := by
  obtain ⟨w0, hw0⟩ := InfinitePlace.comap_surjective (k := K) (K := E.L) w
  have hw0l : w0.LiesOver w := by subst hw0; infer_instance
  have hrange := hψ.range_infinite E w w0 hw0
  have key := hom_eq_of_card_le_two ((idelicArtinTauCeti E.L).comp (IdeleGroup.ofCompletion (𝓞 K) K w))
    ((ψ E).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) (MulAction.stabilizer Gal(E.L/K) w0)
    (InfinitePlace.nat_card_stabilizer_eq_one_or_two K w0) ?_ hrange ?_
  · exact (DFunLike.congr_fun key z).symm
  · intro t
    have hmem : TauCeti.ClassFieldTheory.infiniteLocalArtinAt K E.L w t ∈ (TauCeti.ClassFieldTheory.infiniteLocalArtinAt K E.L w).range := ⟨t, rfl⟩
    rw [TauCeti.ClassFieldTheory.range_infiniteLocalArtinAt w w0] at hmem
    obtain ⟨s, hs, hseq⟩ := hmem
    have h1 : Abelianization.of (idelicArtinTauCeti E.L (IdeleGroup.ofCompletion (𝓞 K) K w t)) =
        TauCeti.ClassFieldTheory.infiniteLocalArtinAt K E.L w t := by
      rw [of_idelicArtinTauCeti, TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal]
      rfl
    have h2 : s = idelicArtinTauCeti E.L (IdeleGroup.ofCompletion (𝓞 K) K w t) :=
      Abelianization.of_injective (hseq.trans h1.symm)
    rw [MonoidHom.comp_apply, ← h2]
    exact hs
  · intro t
    exact mem_zpowers_of_local ψ hψ E _ fun F h => mem_normIdeles_of_tc_infinite F w t h

/-- **Uniqueness of the global Artin map**: every family with the properties `IsGlobalArtinMap` is Tau Ceti's
idèlic Artin map. -/
theorem eq_idelicArtinTauCeti (E : AbExt K Ω) : ψ E = idelicArtinTauCeti E.L := by
  refine ideleHom_eq_of_local_open _ _ ?_ (eq_tc_finite ψ hψ E) (eq_tc_infinite ψ hψ E)
  exact IsOpen.inter (hψ.isOpen_ker E) (isOpen_ker_idelicArtinTauCeti E.L)

end T81

/-- **Theorem 8.1 (a)** (Milne, *CFT*, VII, Theorem 8.1 (a), p. 221): every global Artin map is trivial on the
principal idèles. Every family with the properties `IsGlobalArtinMap` equals Tau Ceti's idèlic Artin map
(`T81.eq_idelicArtinTauCeti`), which is trivial on `K^×` (`idelicArtinTauCeti_principal`). -/
@[kb "milne2020cft" "Ch. VII, Thm. 8.1 (a), p. 221"]
theorem theorem8_1a (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] : Theorem8_1a K Ω := by
  refine ⟨fun ψ hψ E => ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, T81.eq_idelicArtinTauCeti ψ hψ E]
  exact idelicArtinTauCeti_principal E.L a

/-- **Example 8.2** (Milne, *CFT*, VII, Example 8.2, p. 221): Theorem 8.1 (a) for the cyclotomic extensions of
`ℚ`, a special case of `theorem8_1a`. -/
@[kb "milne2020cft" "Ch. VII, Example 8.2, p. 221"]
theorem example8_2 (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] : Example8_2 Ω :=
  ⟨fun ψ hψ E _ _ => (theorem8_1a ℚ Ω).principal_le_ker ψ hψ E⟩

end NumberFieldKB.MilneCFT.Ch7
