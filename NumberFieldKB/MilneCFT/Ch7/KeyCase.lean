import NumberFieldKB.MilneCFT.Ch7.Existence
import NumberFieldKB.MilneCFT.Ch7.Lemma42
import NumberFieldKB.MilneCFT.Ch7.Lemma66
import NumberFieldKB.MilneCFT.Ch7.IdeleOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Milne, *Class Field Theory*, Chapter VII, Lemma 9.3 (the key case of the existence theorem)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
Lemma 9.3 (p. 224).

`lemma_9_3_of_section6` proves Lemma 9.3 following Milne: for $S$ finite, containing the primes over $p$, generators of
the class group and the primes where an open subgroup is not yet "unit-like", let $L = K[U(S)^{1/p}]$ and
$E = \prod_{v\in S}K_v^{\times p}\times\prod_{v\notin S}U_v$ ($p$-th powers at the infinite places). Then
(a) $E\subseteq\mathrm{Nm}(\mathbb I_L)$ (Lemma 6.4 with $T=\emptyset$), and (b)
$(\mathbb I_K : K^\times E) = p^s = [L:K] = (\mathbb I_K : K^\times\mathrm{Nm}\,\mathbb I_L)$
(Lemmas 4.2, 6.5, 6.6, Proposition 9.2, Kummer theory, the $S$-unit theorem, the reciprocity law). Hence
$K^\times E = K^\times\mathrm{Nm}(\mathbb I_L)$, and an open $V\subseteq C_K$ with $C_K/V$ killed by $p$ contains the
image of $E$, so contains $\mathrm{Nm}(C_L)$ and is a norm group (Lemma 9.1).

New named inputs: `KummerAppendix` (Kummer theory, Milne's Appendix, Theorem A.3) and `SUnitIndex`
($(U(S):U(S)^p) = p^s$, from the $S$-unit theorem).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **Kummer theory for S-units** (named statement; Milne, *CFT*, Chapter VII, Appendix, Theorem A.3, for the group
$B = U(S)K^{\times p}$; FT 5.29): if $K$ contains a primitive $p$-th root of $1$ and $S$ is finite, containing the
primes over $p$ and class group generators, there is a Galois extension $M = K[U(S)^{1/p}]$ in Milne's setting
(`KummerSetting`), abelian, of degree $(U(S)K^{\times p}:K^{\times p}) = (U(S) : U(S)\cap K^{\times p})$. -/
@[kb "milne2020cft" "Ch. VII, App., Thm. A.3 (input, for B = U(S)K^{×p})"]
structure KummerAppendix : Prop where
  exists_ext : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))), p.Prime → (∃ ζ : K, IsPrimitiveRoot ζ p) →
    S.Finite → (∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤ →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : IsGalois K M),
      (∀ σ τ : Gal(M/K), σ * τ = τ * σ) ∧ KummerSetting p S M ∧
      Module.finrank K M = (powMonoidHom p : Kˣ →* Kˣ).range.relIndex (S.unit K)

/-- **The index of $p$-th powers of $S$-units** (named statement; Milne, *CFT*, Chapter VII, proof of Lemma 9.3,
from the Dirichlet $S$-unit theorem, Milne, *ANT*, Theorem 5.9: $U(S)\cong\mu(K)\times\mathbb Z^{s-1}$): if $K$
contains a primitive $p$-th root of $1$ and $S$ is a finite set of finite primes, $(U(S):U(S)^p) = p^s$,
$s = |S| + $ the number of infinite places. Here $(U(S) : U(S)\cap K^{\times p})$, which is the same group index
since an element of $K^\times$ whose $p$-th power is an $S$-unit is an $S$-unit.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.relIndex_range_powMonoidHom_sUnits_numberField` (`TauCeti/NumberTheory/NumberField/Units/SUnit/Basic.lean:46`)
at Tau Ceti commit `7ed979dc`. Needed to apply it here: Tau Ceti's hypothesis that the number field has enough
`p`-th roots of unity comes from our assumption of a primitive `p`-th root of unity, and the cardinality of our set of
primes is the cardinality of the corresponding finite set there. -/
@[kb "milne2020cft" "Ch. VII, proof of Lemma 9.3 (S-unit theorem, ANT 5.9; input)"]
structure SUnitIndex : Prop where
  index : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))), p.Prime → (∃ ζ : K, IsPrimitiveRoot ζ p) → S.Finite →
    (powMonoidHom p : Kˣ →* Kˣ).range.relIndex (S.unit K) = p ^ (S.ncard + Fintype.card (InfinitePlace K))

variable {K}

/-! ## The reciprocity law: the index of the norm classes -/

/-- From the reciprocity law: $(C_K : \mathrm{Nm}(C_M)) = [M:K]$ for $M/K$ finite abelian. -/
theorem index_normClasses (hR : ReciprocityLaw K) (M : Type) [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hc : ∀ σ τ : Gal(M/K), σ * τ = τ * σ) :
    (normClasses K M).index = Module.finrank K M := by
  obtain ⟨ψ, hsurj, hker, -⟩ := hR.exists_artin M hc
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj]
  rw [Nat.card_congr (Subgroup.topEquiv (G := Gal(M/K))).toEquiv]
  exact IsGalois.card_aut_eq_finrank K M

/-- From the reciprocity law: $\mathrm{Nm}(C_{\top}) = \mathrm{Nm}(C_M)$ for the top intermediate field. -/
theorem normClasses_top (hR : ReciprocityLaw K) (M : Type) [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hc : ∀ σ τ : Gal(M/K), σ * τ = τ * σ) :
    normClasses K (⊤ : IntermediateField K M) = normClasses K M := by
  have : Normal K (⊤ : IntermediateField K M) := Normal.of_algEquiv (IntermediateField.topEquiv (F := K) (E := M)).symm
  obtain ⟨ψ, hsurj, hker, hres⟩ := hR.exists_artin M hc
  rw [← hres ⊤, ← hker]
  let f : Gal(M/K) →* ((⊤ : IntermediateField K M) ≃ₐ[K] (⊤ : IntermediateField K M)) :=
    AlgEquiv.restrictNormalHom _
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact (IntermediateField.restrictNormalHom_ker (⊤ : IntermediateField K M)).trans
      IntermediateField.fixingSubgroup_top
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [← map_one f]
  exact hinj.eq_iff

/-! ## (a) $E\subseteq\mathrm{Nm}(\mathbb I_L)$ -/

/-- Lemma 6.4 with $T = \emptyset$ and $L = M$: $E\subseteq\mathrm{Nm}(\mathbb I_M)$, i.e. the image of $E$ in
$C_K$ lies in $\mathrm{Nm}(C_M)$. -/
theorem map_kummerE_le_normClasses (hR : ReciprocityLaw K) {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))}
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] (hc : ∀ σ τ : Gal(M/K), σ * τ = τ * σ)
    (h64 : Lemma6_4 p S M) (hset : KummerSetting p S M) :
    (kummerE S ∅ p).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) ≤ normClasses K M := by
  let Q : ∀ v : (∅ : Finset (HeightOneSpectrum (𝓞 K))), v.1.asIdeal.primesOver (𝓞 M) :=
    fun v => absurd v.2 (Finset.notMem_empty _)
  have hF : FrobBasis p (⊤ : IntermediateField K M) ∅ Q := by
    have hsub : ∀ e : (∅ : Finset (HeightOneSpectrum (𝓞 K))) → ZMod p,
        (((Finset.univ : Finset (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toList.map fun v =>
          frobAt K M v.1 (Q v) ^ (e v).val).prod) = 1 := by
      intro e
      have : (Finset.univ : Finset (∅ : Finset (HeightOneSpectrum (𝓞 K)))) = ∅ := by
        ext v; exact absurd v.2 (Finset.notMem_empty _)
      simp
    refine ⟨fun e _ => ?_, fun e _ e' _ _ => ?_, fun g hg => ⟨fun v => absurd v.2 (Finset.notMem_empty _), trivial, ?_⟩⟩
    · beta_reduce
      rw [hsub e, SetLike.mem_coe, IntermediateField.fixingSubgroup_top]; exact Subgroup.one_mem _
    · funext v; exact absurd v.2 (Finset.notMem_empty _)
    · beta_reduce
      rw [hsub]
      have : g ∈ (⊤ : IntermediateField K M).fixingSubgroup := hg
      rw [IntermediateField.fixingSubgroup_top] at this
      exact (Subgroup.mem_bot.1 this).symm
  have hle := (h64.le hset ⊤ ∅ Q (by simp) (by simp) hF)
  rw [Finset.coe_empty] at hle
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, rfl⟩ := hle hx
  rw [← normClasses_top hR M hc]
  exact ⟨QuotientGroup.mk y, rfl⟩

/-! ## (b) the index of $K^\times E$ -/

/-- $(\mathbb I_K : K^\times E) = p^s$ (Lemmas 4.2, 6.5, 6.6, Proposition 9.2 and the $S$-unit index). -/
theorem index_kummerE_sup (h68 : Prop6_8 K) (h610 : Prop6_10 K) (hSU : SUnitIndex K) {p : ℕ}
    {S : Set (HeightOneSpectrum (𝓞 K))} (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (hset : KummerSetting p S M) :
    (kummerE S ∅ p ⊔ IdeleGroup.principalSubgroup (𝓞 K) K).index =
      p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
  classical
  have hp : 0 < p := hset.prime.pos
  set A := idelesS S with hA
  set B := kummerE S ∅ p with hB
  set C := IdeleGroup.principalSubgroup (𝓞 K) K with hC
  set f := IdeleGroup.unitEmbedding (𝓞 K) K with hf
  have hBA : B ≤ A := fun x hx v hv => hx.2.2 v hv (by simp)
  have h65 := lemma_6_5 (C := C) hBA
  have hAC : A ⊔ C = ⊤ := by rw [sup_comm]; exact lemma_4_2 K S hset.classGroup
  have h66 : B.relIndex A = p ^ (2 * (S.ncard + Fintype.card (InfinitePlace K))) := by
    have := (lemma_6_6_of_prop_6_8 h68 p S M).index hset ∅ (by simp)
    simpa using this
  have hfinj : Function.Injective f := (item_4_2 (K := K)).1
  have hCrange : C = f.range := rfl
  have hmemA : ∀ a : Kˣ, f a ∈ A ↔ a ∈ S.unit K := by
    intro a
    refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
    · have := h v hv
      change Valued.v (((a : K) : v.adicCompletion K)) = 1 at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] 
      exact this
    · have := h v hv
      change Valued.v (((a : K) : v.adicCompletion K)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (a : K)]
      exact this
  have hinfC : A ⊓ C = (S.unit K).map f := by
    ext x
    constructor
    · rintro ⟨hxA, c, rfl⟩
      exact ⟨c, (hmemA c).1 hxA, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(hmemA c).2 hc, c, rfl⟩
  have hBC : B ⊓ C = ((powMonoidHom p : Kˣ →* Kˣ).range ⊓ S.unit K).map f := by
    ext x
    constructor
    · rintro ⟨hxB, c, rfl⟩
      have hcS : c ∈ S.unit K := (hmemA c).1 (hBA hxB)
      refine ⟨c, ⟨?_, hcS⟩, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hxB
      obtain ⟨d, hd⟩ := prop_9_2 K h610 p hp hset.zeta S hset.finite hset.dvd hset.classGroup c
        (fun w => by obtain ⟨y, hy⟩ := h1 w; exact ⟨y, hy⟩)
        (fun v hv => by obtain ⟨y, hy⟩ := h2 v hv; exact ⟨y, hy⟩)
        (fun v hv => by
          have := h3 v hv (by simp)
          change Valued.v (((c : K) : v.adicCompletion K)) = 1 at this
          rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (c : K)] at this)
      exact ⟨d, hd⟩
    · rintro ⟨c, ⟨⟨d, rfl⟩, hcS⟩, rfl⟩
      refine ⟨⟨fun w => ⟨ideleInfAt (f d) w, ?_⟩, fun v _ => ⟨ideleFinAt (f d) v, ?_⟩, fun v hv _ => ?_⟩, _, rfl⟩
      · show _ = (↑(f (d ^ p)) : AdeleRing (𝓞 K) K).1 w
        rw [map_pow, Units.val_pow_eq_pow_val]; rfl
      · show _ = (↑(f (d ^ p)) : AdeleRing (𝓞 K) K).2 v
        rw [map_pow, Units.val_pow_eq_pow_val]; rfl
      · exact (hmemA _).2 hcS v hv
  have hrel2 : (B ⊓ C).relIndex (A ⊓ C) = p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
    rw [hinfC, hBC, Subgroup.relIndex_map_map_of_injective _ _ hfinj, Subgroup.inf_relIndex_right]
    exact hSU.index p S hset.prime hset.zeta hset.finite
  rw [hAC, Subgroup.relIndex_top_right, hrel2, h66] at h65
  have hpos : 0 < p ^ (S.ncard + Fintype.card (InfinitePlace K)) := pow_pos hp _
  have h2s : p ^ (2 * (S.ncard + Fintype.card (InfinitePlace K))) = p ^ (S.ncard + Fintype.card (InfinitePlace K)) * p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by rw [two_mul, pow_add]
  rw [h2s] at h65
  exact Nat.eq_of_mul_eq_mul_right hpos h65

/-! ## Lemma 9.3 -/

/-- An open subgroup $U$ of $\mathbb I_K$ containing $\mathbb I_K^p$ and $\prod_{v\in S}\{1\}\times\prod_{v\notin S}U_v$
contains $E$ (write $x\in E$ as $y^p z$). -/
theorem kummerE_le_of_pow {p : ℕ} (hp : 0 < p) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (U : Subgroup (IdeleGroup (𝓞 K) K)) (hpow : ∀ y : IdeleGroup (𝓞 K) K, y ^ p ∈ U)
    (hU : ∀ x : IdeleGroup (𝓞 K) K, (∀ w : InfinitePlace K, (x : AdeleRing (𝓞 K) K).1 w = 1) →
      (∀ v ∈ S, (x : AdeleRing (𝓞 K) K).2 v = 1) →
      (∀ v, Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1) → x ∈ U) :
    kummerE S ∅ p ≤ U := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  have hinf : ∀ w : InfinitePlace K, ∃ d : w.Completionˣ, d ^ p = infUnit w x := fun w =>
    (mem_range_pow_iff hp (infUnit w x)).2 (by simpa [coe_infUnit] using h1 w)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ d : (v.adicCompletion K)ˣ, v ∈ S → d ^ p = finUnit v x := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨d, hd⟩ := (mem_range_pow_iff hp (finUnit v x)).2 (by rw [coe_finUnit]; exact h2 v hv)
      exact ⟨d, fun _ => hd⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose d hd using hinf
  choose d' hd' using hfin
  set y : IdeleGroup (𝓞 K) K := (∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (d w)) *
    ∏ v ∈ hS.toFinset, IdeleGroup.ofAdicCompletion (𝓞 K) K v (d' v) with hy
  have hA : ∀ w, infUnit w y = d w := by
    intro w
    rw [hy, map_mul, map_prod, map_prod, Finset.prod_eq_single_of_mem w (Finset.mem_univ w)]
    · rw [Finset.prod_eq_one, mul_one]
      · exact Units.ext (ideleInfAt_ofCompletion_self w (d w))
      · intro v _; exact Units.ext (ofAdicCompletion_infAt v _ w)
    · intro w' _ hne; exact Units.ext (ideleInfAt_ofCompletion_ne w' w hne.symm _)
  have hB : ∀ v ∈ S, finUnit v y = d' v := by
    intro v hv
    rw [hy, map_mul, map_prod, map_prod, Finset.prod_eq_one (s := Finset.univ), one_mul,
      Finset.prod_eq_single_of_mem v (hS.mem_toFinset.2 hv)]
    · exact Units.ext (ofAdicCompletion_finAt_self v (d' v))
    · intro v' _ hne; exact Units.ext (ofAdicCompletion_finAt_ne (Ne.symm hne) _)
    · intro w _; exact Units.ext (ideleFinAt_ofCompletion w _ v)
  have hC : ∀ v ∉ S, finUnit v y = 1 := by
    intro v hv
    rw [hy, map_mul, map_prod, map_prod, Finset.prod_eq_one (s := Finset.univ), one_mul]
    · exact Finset.prod_eq_one fun v' hv' => Units.ext
        (ofAdicCompletion_finAt_ne (fun h => hv (by rw [h]; exact hS.mem_toFinset.1 hv')) _)
    · intro w _; exact Units.ext (ideleFinAt_ofCompletion w _ v)
  have hxy : x = (x * (y ^ p)⁻¹) * y ^ p := by group
  rw [hxy]
  refine U.mul_mem (hU _ ?_ ?_ ?_) (hpow y)
  · intro w
    have : infUnit w (x * (y ^ p)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hA, hd w, mul_inv_cancel]
    exact congrArg Units.val this
  · intro v hv
    have : finUnit v (x * (y ^ p)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hB v hv, hd' v hv, mul_inv_cancel]
    exact congrArg Units.val this
  · intro v
    by_cases hv : v ∈ S
    · have : finUnit v (x * (y ^ p)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_pow, hB v hv, hd' v hv, mul_inv_cancel]
      have := congrArg Units.val this
      rw [coe_finUnit] at this
      rw [this]; exact map_one _
    · have : finUnit v (x * (y ^ p)⁻¹) = finUnit v x := by
        rw [map_mul, map_inv, map_pow, hC v hv, one_pow, inv_one, mul_one]
      have h' : Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1 := h3 v hv (by simp)
      have := congrArg Units.val this
      rw [coe_finUnit, coe_finUnit] at this
      rw [this]; exact h'

variable (K) in
/-- **Lemma 9.3** (Milne, *CFT*, Chapter VII, p. 224), from Milne's proof: conditional on the reciprocity law,
Lemma 6.4, Proposition 6.8, Proposition 6.10, Kummer theory (`KummerAppendix`) and the $S$-unit index
(`SUnitIndex`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.3 (proof)"]
theorem lemma_9_3_of_section6 (hR : ReciprocityLaw K)
    (h64 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
      [Algebra K M] [IsGalois K M], Lemma6_4 p S M)
    (h68 : Prop6_8 K) (h610 : Prop6_10 K) (hKum : KummerAppendix K) (hSU : SUnitIndex K) : Lemma9_3 K := by
  classical
  refine ⟨fun p hp hζ V hVo _ hVpow => ?_⟩
  set π := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) with hπ
  set U := V.comap π with hU
  have hUo : IsOpen (U : Set (IdeleGroup (𝓞 K) K)) := hVo.preimage QuotientGroup.continuous_mk
  have hUpow : ∀ y : IdeleGroup (𝓞 K) K, y ^ p ∈ U := fun y => by
    show π (y ^ p) ∈ V
    rw [map_pow]; exact hVpow _
  obtain ⟨S₀, hS₀⟩ := exists_finset_of_isOpen U hUo
  obtain ⟨S₁, hS₁fin, hS₁cl⟩ := exists_finite_classGroup_generators K
  set S : Set (HeightOneSpectrum (𝓞 K)) :=
    (↑S₀ ∪ {v | (p : 𝓞 K) ∈ v.asIdeal}) ∪ S₁ with hSdef
  have hSfin : S.Finite :=
    ((S₀.finite_toSet.union (finite_primes_dvd K p hp.ne_zero)).union hS₁fin)
  have hSdvd : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => Or.inl (Or.inr hv)
  have hScl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤ := by
    rw [eq_top_iff, ← hS₁cl]
    exact Subgroup.closure_mono (Set.image_mono Set.subset_union_right)
  obtain ⟨M, iF, iN, iA, iG, hc, hset, hfr⟩ := hKum.exists_ext p S hp hζ hSfin hSdvd hScl
  have hfr' : Module.finrank K M = p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
    rw [hfr]; exact hSU.index p S hp hζ hSfin
  have hE1 := map_kummerE_le_normClasses hR M hc (h64 p S M) hset
  have hEU : kummerE S ∅ p ≤ U := by
    refine kummerE_le_of_pow hp.pos S hSfin U hUpow (fun x h1 h2 h3 => hS₀ x h1 (fun v hv => h2 v ?_) h3)
    exact Or.inl (Or.inl hv)
  have hEV : (kummerE S ∅ p).map π ≤ V := Subgroup.map_le_iff_le_comap.2 hEU
  have hidx : ((kummerE S ∅ p).map π).index = p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
    have h := Subgroup.index_comap_of_surjective ((kummerE S ∅ p).map π) (f := π)
      (QuotientGroup.mk'_surjective _)
    rw [← h, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
    exact index_kummerE_sup h68 h610 hSU M hset
  have hpos : 0 < p ^ (S.ncard + Fintype.card (InfinitePlace K)) := pow_pos hp.pos _
  have hrel := Subgroup.relIndex_mul_index hE1
  rw [hidx, index_normClasses hR M hc, hfr'] at hrel
  have h1 : ((kummerE S ∅ p).map π).relIndex (normClasses K M) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hrel.trans (one_mul _).symm)
    exact this
  have hle : normClasses K M ≤ (kummerE S ∅ p).map π := Subgroup.relIndex_eq_one.1 h1
  exact lemma_9_1 K hR ⟨M, iF, iN, iA, iG, hc, rfl⟩ (hle.trans hEV)

end NumberFieldKB.MilneCFT.Ch7
