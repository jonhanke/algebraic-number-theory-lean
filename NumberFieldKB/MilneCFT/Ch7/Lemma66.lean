import NumberFieldKB.MilneCFT.Ch7.KummerSetting
import NumberFieldKB.MilneCFT.Ch5Ideles
import NumberFieldKB.MilneCFT.Ch5Density
import NumberFieldKB.MilneCFT.Ch5IdelesChar

/-!
# Milne, *Class Field Theory*, Chapter VII, Lemma 6.6 from Proposition 6.8

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

We prove $(\mathbb I_{S\cup T} : E) = p^{2s}$ (`lemma_6_6_of_prop_6_8`) from the local indexes of Proposition 6.8.
The subgroup $E$ imposes `p`-th power conditions at finitely many places only; we compute its index in
$\mathbb I_{S\cup T}$ by adding one place at a time (`relIndex_inf_comap`), each step contributing the local index
$(K_v^\times:K_v^{\times p})$.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
  NumberFieldKB.Ideles NumberFieldKB.MilneCFT
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-! ## The product of the norms $N(v)^{\mathrm{ord}_v p}$ -/

/-- $\prod_{v\in S}N(v)^{\mathrm{ord}_v p} = p^{[K:\mathbb Q]}$ when $S$ contains every $v\mid p$. -/
theorem prod_absNorm_pow_ordNat {S : Finset (HeightOneSpectrum (𝓞 K))} {p : ℕ} (hp : 0 < p)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ ordNat K v p = p ^ Module.finrank ℚ K := by
  have hne : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne'
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hne
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      v.maxPowDividing (Ideal.span {(p : 𝓞 K)})) ⊆ ↑S := by
    intro v hv
    by_contra hvS
    apply hv
    have h0 : ordNat K v p = 0 := by
      by_contra h0
      apply hvS
      apply hS
      have hdvd : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
        (Associates.count_ne_zero_iff_dvd hne v.irreducible).1 h0
      exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 hdvd)
    show v.asIdeal ^ ordNat K v p = 1
    rw [h0, pow_zero]
  have h1 : ∏ v ∈ S, v.maxPowDividing (Ideal.span {(p : 𝓞 K)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
    exact hfac
  have h2 := congrArg Ideal.absNorm h1
  rw [map_prod] at h2
  have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) p by simp, Algebra.norm_algebraMap]
    rw [this]
    rw [NumberField.RingOfIntegers.rank]
    simp
  rw [← h3, ← h2]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
  rfl

/-! ## Local indexes -/

/-- The index of the $n$-th powers is invariant under isomorphism. -/
theorem index_pow_range_equiv {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_map_equiv (powMonoidHom n : G →* G).range e]
  congr 1
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨e.symm a, rfl⟩, by simp⟩

/-- A field with a primitive $p$-th root of unity has $p$ roots of unity of order $p$. -/
theorem numRootsOfUnity_eq {F : Type*} [Field F] {p : ℕ} (hp : 0 < p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) : numRootsOfUnity F p = p := by
  have : NeZero p := ⟨hp.ne'⟩
  exact hζ.card_rootsOfUnity

/-- Local index at a finite prime, given $\zeta_p\in K$ (Proposition 6.8). -/
theorem finite_local_index (h68 : Prop6_8 K) {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index =
      p * p * Ideal.absNorm v.asIdeal ^ ordNat K v p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have h := hζ.map_of_injective (f := algebraMap K (v.adicCompletion K)) (RingHom.injective _)
  rw [h68.index_pow v p hp, numRootsOfUnity_eq hp h]

/-- Local index at a complex place: $1$. -/
theorem complex_local_index {p : ℕ} (hp : 0 < p) (w : InfinitePlace K) (hw : w.IsComplex) :
    (powMonoidHom p : w.Completionˣ →* w.Completionˣ).range.index = 1 := by
  rw [index_pow_range_equiv (Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv)]
  have h := prop_6_8_complex p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hc : numRootsOfUnity ℂ p = p := by
    have : NeZero p := ⟨hp.ne'⟩
    exact Complex.card_rootsOfUnity p
  rw [hc] at h
  have : ((powMonoidHom p : ℂˣ →* ℂˣ).range.index : ℚ) = 1 := by
    rw [h]; field_simp
  exact_mod_cast this

/-- Local index at a real place, given $\zeta_p\in K$: $p$ (in fact $p = 2$). -/
theorem real_local_index {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (w : InfinitePlace K) (hw : w.IsReal) :
    (powMonoidHom p : w.Completionˣ →* w.Completionˣ).range.index = p := by
  rw [index_pow_range_equiv (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv)]
  have h := prop_6_8_real p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' := hζ.map_of_injective (f := ((InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).comp (algebraMap K w.Completion))) (RingHom.injective _)
  rw [numRootsOfUnity_eq hp hζ'] at h
  have : ((powMonoidHom p : ℝˣ →* ℝˣ).range.index : ℚ) = p := by
    rw [h]; field_simp
  exact_mod_cast this

/-! ## Adding one place at a time -/

/-- If $f$ maps $R$ onto $A$ then the preimage of $N$ has index $(A:N)$ in $R$. -/
theorem relIndex_inf_comap {X A : Type*} [Group X] [Group A] (R : Subgroup X) (f : X →* A) (N : Subgroup A)
    (hsurj : ∀ a, ∃ x ∈ R, f x = a) : (R ⊓ N.comap f).relIndex R = N.index := by
  rw [Subgroup.relIndex]
  have : (R ⊓ N.comap f).subgroupOf R = N.comap (f.comp R.subtype) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [this]
  apply Subgroup.index_comap_of_surjective
  intro a
  obtain ⟨x, hx, rfl⟩ := hsurj a
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The component at a finite prime $v$ as a homomorphism to $K_v^\times$. -/
def finUnit (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ where
  toFun x := ⟨ideleFinAt x v, ideleFinAt x⁻¹ v, by rw [← ideleFinAt_mul, mul_inv_cancel, ideleFinAt_one],
    by rw [← ideleFinAt_mul, inv_mul_cancel, ideleFinAt_one]⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl

/-- The component at an infinite place $w$ as a homomorphism to $K_w^\times$. -/
def infUnit (w : InfinitePlace K) : IdeleGroup (𝓞 K) K →* w.Completionˣ where
  toFun x := ⟨ideleInfAt x w, ideleInfAt x⁻¹ w, by rw [← ideleInfAt_mul, mul_inv_cancel, ideleInfAt_one],
    by rw [← ideleInfAt_mul, inv_mul_cancel, ideleInfAt_one]⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl

theorem coe_finUnit (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    ((finUnit v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : AdeleRing (𝓞 K) K).2 v := rfl

theorem coe_infUnit (w : InfinitePlace K) (x : IdeleGroup (𝓞 K) K) :
    ((infUnit w x : w.Completionˣ) : w.Completion) = (x : AdeleRing (𝓞 K) K).1 w := rfl

/-- A unit of a field is an $n$-th power of a unit iff it is an $n$-th power. -/
theorem mem_range_pow_iff {F : Type*} [Field F] {n : ℕ} (hn : 0 < n) (u : Fˣ) :
    u ∈ (powMonoidHom n : Fˣ →* Fˣ).range ↔ ∃ y : F, y ^ n = (u : F) := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, by simp⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hy
      exact u.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

/-- Ideles whose component at the infinite place $w$ is a $p$-th power. -/
def Ninf (p : ℕ) (w : InfinitePlace K) : Subgroup (IdeleGroup (𝓞 K) K) :=
  (powMonoidHom p : w.Completionˣ →* w.Completionˣ).range.comap (infUnit w)

/-- Ideles whose component at the finite prime $v$ is a $p$-th power. -/
def Nfin (p : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Subgroup (IdeleGroup (𝓞 K) K) :=
  (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.comap (finUnit v)

/-- $\mathbb I_{S\cup T}$ with $p$-th power conditions at the infinite places in $P$. -/
def E1 (p : ℕ) (U : Set (HeightOneSpectrum (𝓞 K))) (P : Finset (InfinitePlace K)) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  idelesS U ⊓ ⨅ w ∈ P, Ninf p w

/-- The previous group with, in addition, $p$-th power conditions at the finite primes in $Q$. -/
def E2 (p : ℕ) (U : Set (HeightOneSpectrum (𝓞 K))) (Q : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  E1 p U Finset.univ ⊓ ⨅ v ∈ Q, Nfin p v

theorem ofCompletion_mem_idelesS (U : Set (HeightOneSpectrum (𝓞 K))) (w : InfinitePlace K)
    (u : w.Completionˣ) : IdeleGroup.ofCompletion (𝓞 K) K w u ∈ idelesS U := by
  intro v _
  have := ideleFinAt_ofCompletion w u v
  change Valued.v (ideleFinAt _ v) = 1
  rw [this, map_one]

theorem ofAdicCompletion_mem_idelesS {U : Set (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ U) (u : (v.adicCompletion K)ˣ) : IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈ idelesS U := by
  intro w hw
  have hne : w ≠ v := fun h => hw (h ▸ hv)
  have := ofAdicCompletion_finAt_ne hne u
  change Valued.v (ideleFinAt _ w) = 1
  rw [this, map_one]

theorem index_E1 (p : ℕ) (U : Set (HeightOneSpectrum (𝓞 K)))
    (idx : InfinitePlace K → ℕ)
    (hidx : ∀ w, (powMonoidHom p : w.Completionˣ →* w.Completionˣ).range.index = idx w)
    (P : Finset (InfinitePlace K)) :
    (E1 p U P).relIndex (idelesS U) = ∏ w ∈ P, idx w := by
  induction P using Finset.induction_on with
  | empty => simp [E1]
  | insert a P ha ih =>
    have hE : E1 p U (insert a P) = E1 p U P ⊓ (Ninf p a) := by
      ext x
      simp only [E1, Subgroup.mem_inf, Subgroup.mem_iInf, Finset.mem_insert, forall_eq_or_imp]
      tauto
    have hle : E1 p U (insert a P) ≤ E1 p U P := by
      rw [hE]; exact inf_le_left
    have hle2 : E1 p U P ≤ idelesS U := inf_le_left
    have hstep : (E1 p U (insert a P)).relIndex (E1 p U P) = idx a := by
      rw [hE, ← hidx a]
      apply relIndex_inf_comap (E1 p U P) (infUnit a)
      intro u
      refine ⟨IdeleGroup.ofCompletion (𝓞 K) K a u, ⟨ofCompletion_mem_idelesS U a u, ?_⟩, ?_⟩
      · show _ ∈ (⨅ w ∈ P, Ninf p w)
        rw [Subgroup.mem_iInf]
        intro b
        rw [Subgroup.mem_iInf]
        intro hb
        have hba : b ≠ a := fun h => ha (h ▸ hb)
        show _ ∈ Ninf p b
        have : infUnit b (IdeleGroup.ofCompletion (𝓞 K) K a u) = 1 :=
          Units.ext (ideleInfAt_ofCompletion_ne a b hba u)
        show infUnit b _ ∈ (powMonoidHom p : b.Completionˣ →* b.Completionˣ).range
        rw [this]; exact one_mem _
      · exact Units.ext (ideleInfAt_ofCompletion_self a u)
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hle2, hstep, ih, Finset.prod_insert ha, mul_comm]

theorem index_E2 (p : ℕ) (U : Set (HeightOneSpectrum (𝓞 K)))
    (idx : HeightOneSpectrum (𝓞 K) → ℕ)
    (hidx : ∀ v, (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index = idx v)
    (Q : Finset (HeightOneSpectrum (𝓞 K))) (hQ : ∀ v ∈ Q, v ∈ U) :
    (E2 p U Q).relIndex (E1 p U Finset.univ) = ∏ v ∈ Q, idx v := by
  induction Q using Finset.induction_on with
  | empty => simp [E2]
  | insert a Q ha ih =>
    have hQ' : ∀ v ∈ Q, v ∈ U := fun v hv => hQ v (Finset.mem_insert_of_mem hv)
    have hE : E2 p U (insert a Q) = E2 p U Q ⊓ (Nfin p a) := by
      ext x
      simp only [E2, Subgroup.mem_inf, Subgroup.mem_iInf, Finset.mem_insert, forall_eq_or_imp]
      tauto
    have hle : E2 p U (insert a Q) ≤ E2 p U Q := by
      rw [hE]; exact inf_le_left
    have hle2 : E2 p U Q ≤ E1 p U Finset.univ := inf_le_left
    have hstep : (E2 p U (insert a Q)).relIndex (E2 p U Q) = idx a := by
      rw [hE, ← hidx a]
      apply relIndex_inf_comap (E2 p U Q) (finUnit a)
      intro u
      have haU : a ∈ U := hQ a (Finset.mem_insert_self a Q)
      refine ⟨IdeleGroup.ofAdicCompletion (𝓞 K) K a u, ⟨⟨ofAdicCompletion_mem_idelesS haU u, ?_⟩, ?_⟩, ?_⟩
      · show _ ∈ (⨅ w ∈ (Finset.univ : Finset (InfinitePlace K)), Ninf p w)
        rw [Subgroup.mem_iInf]
        intro b
        rw [Subgroup.mem_iInf]
        intro _
        show _ ∈ Ninf p b
        have : infUnit b (IdeleGroup.ofAdicCompletion (𝓞 K) K a u) = 1 :=
          Units.ext (ofAdicCompletion_infAt a u b)
        show infUnit b _ ∈ (powMonoidHom p : b.Completionˣ →* b.Completionˣ).range
        rw [this]; exact one_mem _
      · show _ ∈ (⨅ w ∈ Q, Nfin p w)
        rw [Subgroup.mem_iInf]
        intro b
        rw [Subgroup.mem_iInf]
        intro hb
        have hba : b ≠ a := fun h => ha (h ▸ hb)
        show _ ∈ Nfin p b
        have : finUnit b (IdeleGroup.ofAdicCompletion (𝓞 K) K a u) = 1 :=
          Units.ext (ofAdicCompletion_finAt_ne hba u)
        show finUnit b _ ∈ (powMonoidHom p : (b.adicCompletion K)ˣ →* (b.adicCompletion K)ˣ).range
        rw [this]; exact one_mem _
      · exact Units.ext (ofAdicCompletion_finAt_self a u)
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hle2, hstep, ih hQ', Finset.prod_insert ha, mul_comm]

/-! ## Lemma 6.6 -/

theorem kummerE_eq_E2 {p : ℕ} (hp : 0 < p) (S T : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    kummerE S T p = E2 p (S ∪ T) hS.toFinset := by
  ext x
  simp only [E2, E1, Subgroup.mem_inf, Subgroup.mem_iInf, Finset.mem_univ, forall_true_left,
    Set.Finite.mem_toFinset]
  have hinf : ∀ w : InfinitePlace K, x ∈ Ninf p w ↔ ∃ y : w.Completion, y ^ p = (x : AdeleRing (𝓞 K) K).1 w :=
    fun w => mem_range_pow_iff hp (infUnit w x)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), x ∈ Nfin p v ↔ ideleIsPowAt v p x :=
    fun v => mem_range_pow_iff hp (finUnit v x)
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun v hv => h3 v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h)), fun w => (hinf w).2 (h1 w)⟩,
      fun v hv => (hfin v).2 (h2 v hv)⟩
  · rintro ⟨⟨h3, h1⟩, h2⟩
    exact ⟨fun w => (hinf w).1 (h1 w), fun v hv => (hfin v).1 (h2 v hv),
      fun v hvS hvT => h3 v (by rintro (h | h) <;> contradiction)⟩

/-- **Lemma 6.6** (Milne, *CFT*, Chapter VII, p. 217), from Proposition 6.8: $(\mathbb I_{S\cup T} : E) = p^{2s}$,
where $s$ is the number of primes in $S$ together with the infinite primes. The index is the product of the local
indexes $(K_v^\times:K_v^{\times p})$ over the infinite places and the primes in $S$, computed by Proposition 6.8
(`finite_local_index`, `real_local_index`, `complex_local_index`); the finite factors $N(v)^{\mathrm{ord}_v p}$
multiply to $p^{[K:\mathbb Q]}$ (`prod_absNorm_pow_ordNat`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.6 (from Prop. 6.8)"]
theorem lemma_6_6_of_prop_6_8 (h68 : Prop6_8 K) (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type)
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_6 p S M := by
  refine ⟨fun hset T _ => ?_⟩
  have hpp : p.Prime := hset.prime
  have hp : 0 < p := hpp.pos
  have hSf := hset.finite
  rw [kummerE_eq_E2 hp S T hSf]
  let idxF : HeightOneSpectrum (𝓞 K) → ℕ := fun v => p * p * Ideal.absNorm v.asIdeal ^ ordNat K v p
  let idxI : InfinitePlace K → ℕ := fun w => if w.IsReal then p else 1
  have hle1 : E2 p (S ∪ T) hSf.toFinset ≤ E1 p (S ∪ T) Finset.univ := inf_le_left
  have hle2 : E1 p (S ∪ T) Finset.univ ≤ idelesS (S ∪ T) := inf_le_left
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    index_E2 p (S ∪ T) idxF (fun v => finite_local_index h68 hp hset.zeta v) hSf.toFinset
      (fun v hv => Or.inl (hSf.mem_toFinset.1 hv)),
    index_E1 p (S ∪ T) idxI (fun w => by
      by_cases hw : w.IsReal
      · simp only [idxI, hw, ite_true]; exact real_local_index hp hset.zeta w hw
      · simp only [idxI, hw, ite_false]
        exact complex_local_index hp w (InfinitePlace.not_isReal_iff_isComplex.1 hw))]
  have hF : ∏ v ∈ hSf.toFinset, idxF v = p ^ (2 * S.ncard) * p ^ Module.finrank ℚ K := by
    simp only [idxF]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← prod_absNorm_pow_ordNat hp
      (fun v hv => hSf.mem_toFinset.2 (hset.dvd v hv)), ← Set.ncard_eq_toFinset_card S hSf,
      ← pow_two, ← pow_mul]
  have hI : ∏ w : InfinitePlace K, idxI w = p ^ (InfinitePlace.nrRealPlaces K) := by
    simp only [idxI]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, InfinitePlace.nrRealPlaces,
      Fintype.card_subtype]
  rw [hF, hI, ← pow_add, ← pow_add, ← InfinitePlace.card_add_two_mul_card_eq_rank K,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  congr 1
  ring

end NumberFieldKB.MilneCFT.Ch7
