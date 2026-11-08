import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Weil, *Basic Number Theory*, III.§4, Cor. 4 of Thm. 4: Galois extensions and completions (finite places)

$k'/k$ is a Galois extension of number fields (`K/k`, `[IsGalois k K]`) with group $G$, $v$ a finite place of $k$ and
$w$ a finite place of $k'$ above $v$ (`underPlace w = v`). Weil's image of a place under $\sigma\in G$ is the place
of the embedding $\iota\circ\sigma$: $|x|_{\sigma w}=|\sigma x|_w$. For prime ideals, $\sigma w=\sigma^{-1}(w)$
(`galPlace σ w`: $x\in\sigma w\iff\sigma(x)\in w$).

* `underPlace_galPlace`: $\sigma w$ lies over the same place $v$.
* **`weil_III_4_cor4_transitive`**: the places $w_i$ above $v$ are the images of $w$ under $G$.
* **`weil_III_4_cor4_iso`**: the completions $k'_{\sigma w}$ and $k'_w$ are isomorphic: there is a ring isomorphism
  $k'_{\sigma w}\to k'_w$, a homeomorphism, extending $\sigma$ ($x\mapsto\sigma x$ on $k'$) and compatible with the
  embeddings of $k_v$ (`localRingHom`), i.e. an isomorphism over $k_v$.
* **`weil_III_4_cor4_decomposition`**: each $\sigma$ in the decomposition group $\{\sigma:\sigma w=w\}$ extends to a
  continuous automorphism of $k'_w$ over $k_v$, and $\sigma\mapsto$ this extension is an injective group homomorphism.

Not stated: that $k'_w/k_v$ is Galois and every automorphism of $k'_w$ over $k_v$ comes from the decomposition group
(it needs $[k'_w:k_v]=e_wf_w=|D_w|$, the local degree formula, which is not in Mathlib).
-/

open IsDedekindDomain NumberField Filter
open scoped Topology WithZero
open QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The image $\sigma w$ of a finite place $w$ of $k'$ under $\sigma\in\operatorname{Gal}(k'/k)$: the prime ideal
$\sigma^{-1}(w)=\{x:\sigma(x)\in w\}$ of $\mathcal O_{k'}$, so that $|x|_{\sigma w}=|\sigma x|_w$. -/
def galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv (σ : K ≃+* K))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv (σ : K ≃+* K))) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv (σ : K ≃+* K)).surjective,
      Ideal.map_bot] at this

theorem mem_galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (galPlace σ w).asIdeal ↔ RingOfIntegers.mapRingEquiv (σ : K ≃+* K) x ∈ w.asIdeal := Iff.rfl

/-- $(\sigma\tau)w=\tau(\sigma w)$ in this convention ($|x|_{\sigma\tau w}=|\sigma\tau x|_w$). -/
theorem galPlace_mul (σ τ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    galPlace (σ * τ) w = galPlace τ (galPlace σ w) := by
  apply HeightOneSpectrum.ext
  ext x
  exact Iff.rfl

/-- $\sigma w$ lies over the same place of $k$ as $w$. -/
theorem underPlace_galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    underPlace (k := k) (galPlace σ w) = underPlace (k := k) w := by
  apply HeightOneSpectrum.ext
  ext x
  have : RingOfIntegers.mapRingEquiv (σ : K ≃+* K) (algebraMap (𝓞 k) (𝓞 K) x) =
      algebraMap (𝓞 k) (𝓞 K) x := by
    apply Subtype.ext
    exact σ.commutes (x : k)
  show RingOfIntegers.mapRingEquiv (σ : K ≃+* K) (algebraMap (𝓞 k) (𝓞 K) x) ∈ w.asIdeal ↔
    algebraMap (𝓞 k) (𝓞 K) x ∈ w.asIdeal
  rw [this]

/-- **Weil, III.§4, Cor. 4 of Thm. 4** (transitivity): for $k'/k$ Galois, every place $w'$ of $k'$ above the same
place of $k$ as $w$ is $\sigma w$ for some $\sigma\in G$. -/
@[kb "weil1973bnt" "Ch. III, §4, Cor. 4 of Thm. 4 (the places above v are the G-images of w), finite places"]
theorem weil_III_4_cor4_transitive [IsGalois k K] (w w' : HeightOneSpectrum (𝓞 K))
    (h : underPlace (k := k) w' = underPlace (k := k) w) : ∃ σ : K ≃ₐ[k] K, galPlace σ w = w' := by
  have hw : w.asIdeal ∈ Ideal.primesOver (underPlace (k := k) w).asIdeal (𝓞 K) :=
    ⟨w.isPrime, ⟨rfl⟩⟩
  have hw' : w'.asIdeal ∈ Ideal.primesOver (underPlace (k := k) w).asIdeal (𝓞 K) :=
    ⟨w'.isPrime, ⟨by rw [← h]; rfl⟩⟩
  have := Ideal.exists_comap_galRestrict_eq (R := 𝓞 k) (K := k) (L := K) (S := 𝓞 K) hw hw'
  obtain ⟨σ, hσ⟩ := this
  refine ⟨σ, HeightOneSpectrum.ext ?_⟩
  rw [← hσ]
  ext x
  show RingOfIntegers.mapRingEquiv (σ : K ≃+* K) x ∈ w.asIdeal ↔ _
  have : RingOfIntegers.mapRingEquiv (σ : K ≃+* K) x = galRestrict (𝓞 k) k K (𝓞 K) σ x := by
    apply Subtype.ext
    exact (algebraMap_galRestrict_apply (𝓞 k) σ x).symm
  rw [this]
  exact Iff.rfl

theorem continuous_withVal_congr {R S : Type*} [Field R] [Field S]
    (v : Valuation R ℤᵐ⁰) (w : Valuation S ℤᵐ⁰) (hv : Function.Surjective v)
    (f : R ≃+* S) (h : ∀ x, w (f x) = v x) : Continuous (WithVal.congr v w f) := by
  refine continuous_of_tendsto_nhds_zero
    ((WithVal.congr v w f : WithVal v ≃+* WithVal w).toRingHom.toAddMonoidHom) ?_
  show Tendsto (WithVal.congr v w f) (𝓝 0) (𝓝 0)
  rw [(Valued.hasBasis_nhds_zero (WithVal v) ℤᵐ⁰).tendsto_iff (Valued.hasBasis_nhds_zero (WithVal w) ℤᵐ⁰)]
  intro γ _
  obtain ⟨x0, hx0⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hne : (Valued.v : Valuation (WithVal v) ℤᵐ⁰).restrict (WithVal.toVal v x0) ≠ 0 := by
    intro h0
    have := congrArg MonoidWithZeroHom.ValueGroup₀.embedding h0
    rw [Valuation.embedding_restrict, map_zero] at this
    have h1 : γ.1 ≠ 0 := γ.ne_zero
    apply h1
    have h2 := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := ((Valued.v : Valuation (WithVal w) ℤᵐ⁰) : WithVal w →*₀ ℤᵐ⁰))).injective
    apply h2
    rw [map_zero, ← hx0]
    simpa using this
  refine ⟨Units.mk0 _ hne, trivial, ?_⟩
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rw [Units.val_mk0, Valuation.embedding_restrict] at hx
  rw [← hx0]
  exact (h x.ofVal).symm ▸ hx

/-- Powers of the ideal of `σ w` are the preimages of powers of the ideal of `w`. -/
theorem mem_pow_galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : 𝓞 K) :
    x ∈ (galPlace σ w).asIdeal ^ n ↔ RingOfIntegers.mapRingEquiv (σ : K ≃+* K) x ∈ w.asIdeal ^ n := by
  have : (galPlace σ w).asIdeal ^ n = (w.asIdeal ^ n).comap (RingOfIntegers.mapRingEquiv (σ : K ≃+* K)) := by
    show (w.asIdeal.comap _) ^ n = _
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [this]
  exact Iff.rfl

/-- $v_{\sigma w}(r)=v_w(\sigma r)$ on the ring of integers. -/
theorem intValuation_galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (galPlace σ w).intValuation r = w.intValuation (RingOfIntegers.mapRingEquiv (σ : K ≃+* K) r) := by
  set e := RingOfIntegers.mapRingEquiv (σ : K ≃+* K) with he
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : e r ≠ 0 := by simpa using hr
  have key : ∀ n : ℕ, (galPlace σ w).intValuation r ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      mem_pow_galPlace]
  rw [HeightOneSpectrum.intValuation_if_neg _ hr, HeightOneSpectrum.intValuation_if_neg _ hr'] at key ⊢
  set m := (Associates.mk (galPlace σ w).asIdeal).count (Associates.mk (Ideal.span {r} : Ideal (𝓞 K))).factors
  set m' := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e r} : Ideal (𝓞 K))).factors
  have h1 := (key m).1 le_rfl
  have h2 := (key m').2 le_rfl
  rw [WithZero.exp_le_exp] at h1 h2
  have : m = m' := by omega
  rw [this]

/-- $v_{\sigma w}(x)=v_w(\sigma x)$ on $K$. -/
theorem valuation_galPlace (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (galPlace σ w).valuation K x = w.valuation K (σ x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hσ : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv (σ : K ≃+* K) c) :=
    fun c => rfl
  simp only [map_div₀, hσ, HeightOneSpectrum.valuation_of_algebraMap, intValuation_galPlace]


/-- The field embeds in its completion with dense image. -/
theorem denseRange_coe_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    DenseRange (fun x : F => (x : v.adicCompletion F)) := by
  have h1 : DenseRange (fun x : WithVal (v.valuation F) => (x : (v.valuation F).Completion)) :=
    UniformSpace.Completion.denseRange_coe
  have h2 := (HeightOneSpectrum.adicCompletion.ofCompletion_surjective F v).denseRange.comp h1
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion F v)
  have h3 : (fun x : F => (x : v.adicCompletion F)) =
      (HeightOneSpectrum.adicCompletion.ofCompletion ∘ fun x : WithVal (v.valuation F) =>
        (x : (v.valuation F).Completion)) ∘ (WithVal.toVal (v.valuation F)) := rfl
  rw [h3]
  unfold DenseRange
  rw [(WithVal.toVal_surjective _).range_comp]
  exact h2

theorem continuous_congr_gal (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (WithVal.congr ((galPlace σ w).valuation K) (w.valuation K) (σ : K ≃+* K)) :=
  continuous_withVal_congr _ _ ((galPlace σ w).valuation_surjective K) _
    (fun x => (valuation_galPlace σ w x).symm)

theorem continuous_congr_gal_symm (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (WithVal.congr ((galPlace σ w).valuation K) (w.valuation K) (σ : K ≃+* K)).symm := by
  rw [WithVal.congr_symm]
  exact continuous_withVal_congr _ _ (w.valuation_surjective K) _
    (fun y => by
      have := valuation_galPlace σ w ((σ : K ≃+* K).symm y)
      simpa using this)

/-- The ring isomorphism of completions induced by `σ`. -/
def complIso (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    (galPlace σ w).adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K (galPlace σ w)).trans
    (UniformSpace.Completion.mapRingEquiv
      (WithVal.congr ((galPlace σ w).valuation K) (w.valuation K) (σ : K ≃+* K))
      (continuous_congr_gal σ w) (continuous_congr_gal_symm σ w))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

theorem complIso_coe (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    complIso σ w (x : (galPlace σ w).adicCompletion K) = ((σ x : K) : w.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  simp [complIso]
  have hu : UniformContinuous
      (WithVal.congr ((galPlace σ w).valuation K) (w.valuation K) (σ : K ≃+* K)) :=
    uniformContinuous_addMonoidHom_of_continuous
      (f := (WithVal.congr ((galPlace σ w).valuation K) (w.valuation K) (σ : K ≃+* K)).toRingHom.toAddMonoidHom)
      (continuous_congr_gal σ w)
  rw [UniformSpace.Completion.map_coe hu]
  rfl

theorem continuous_complIso (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (complIso σ w) ∧ Continuous (complIso σ w).symm := by
  constructor
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion K _))
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K _).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/-- The isomorphism of completions, for places related by `galPlace σ w₂ = w₁`. -/
theorem iso_aux (σ : K ≃ₐ[k] K) (w₁ w₂ : HeightOneSpectrum (𝓞 K)) (h : galPlace σ w₂ = w₁)
    (v : HeightOneSpectrum (𝓞 k)) (hw₁ : underPlace (k := k) w₁ = v) (hw₂ : underPlace (k := k) w₂ = v) :
    ∃ Φ : w₁.adicCompletion K ≃+* w₂.adicCompletion K,
      Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : K, Φ (x : w₁.adicCompletion K) = ((σ x : K) : w₂.adicCompletion K)) ∧
      ∀ c : v.adicCompletion k, Φ (localRingHom v w₁ hw₁ c) = localRingHom v w₂ hw₂ c := by
  subst h
  refine ⟨complIso σ w₂, (continuous_complIso σ w₂).1, (continuous_complIso σ w₂).2,
    complIso_coe σ w₂, ?_⟩
  have key := DenseRange.equalizer (denseRange_coe_adic v)
    (g := fun c => complIso σ w₂ (localRingHom v (galPlace σ w₂) hw₁ c))
    (h := localRingHom v w₂ hw₂)
    ((continuous_complIso σ w₂).1.comp (continuous_localRingHom v _ hw₁))
    (continuous_localRingHom v _ hw₂) (by
      funext c
      simp only [Function.comp]
      rw [localRingHom_algebraMap, localRingHom_algebraMap, complIso_coe]
      show ((σ (algebraMap k K c) : K) : w₂.adicCompletion K) = _
      rw [σ.commutes c])
  intro c
  exact congrFun key c

/-- The field embeds in its completion injectively. -/
theorem coe_adic_injective {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (fun x : F => (x : v.adicCompletion F)) := by
  intro a b hab
  have := congrArg HeightOneSpectrum.adicCompletion.toCompletion hab
  exact WithVal.toVal_injective _ (UniformSpace.Completion.coe_injective _ this)

/-- **Weil, III.§4, Cor. 4 of Thm. 4** (the completions are isomorphic): $\sigma\in G$ induces a ring isomorphism
$\Phi:k'_{\sigma w}\to k'_w$ which is a homeomorphism, extends $x\mapsto\sigma x$ on $k'$, and is compatible with the
embeddings of $k_v$. -/
@[kb "weil1973bnt" "Ch. III, §4, Cor. 4 of Thm. 4 (all the completions k'_{w_i} are isomorphic), finite places"]
theorem weil_III_4_cor4_iso (σ : K ≃ₐ[k] K) (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 k))
    (hw : underPlace (k := k) w = v) :
    ∃ Φ : (galPlace σ w).adicCompletion K ≃+* w.adicCompletion K,
      Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : K, Φ (x : (galPlace σ w).adicCompletion K) = ((σ x : K) : w.adicCompletion K)) ∧
      ∀ c : v.adicCompletion k,
        Φ (localRingHom v (galPlace σ w) ((underPlace_galPlace σ w).trans hw) c) = localRingHom v w hw c :=
  iso_aux σ _ w rfl v _ hw

/-- **Weil, III.§4, Cor. 4 of Thm. 4** (decomposition group): every $\sigma$ with $\sigma w=w$ extends to a
continuous automorphism of $k'_w$ fixing the image of $k_v$, and this gives an injective homomorphism from the
decomposition group of $w$ into the automorphisms of $k'_w$ over $k_v$. -/
@[kb "weil1973bnt" "Ch. III, §4, Cor. 4 of Thm. 4 (the decomposition group acts faithfully on k'_w over k_v), finite places"]
theorem weil_III_4_cor4_decomposition (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 k))
    (hw : underPlace (k := k) w = v) :
    ∃ ρ : {σ : K ≃ₐ[k] K // galPlace σ w = w} → (w.adicCompletion K ≃+* w.adicCompletion K),
      Function.Injective ρ ∧
      (∀ σ, Continuous (ρ σ) ∧ ∀ x : K, ρ σ (x : w.adicCompletion K) = ((σ.1 x : K) : w.adicCompletion K)) ∧
      (∀ σ τ, ρ ⟨σ.1 * τ.1, by rw [galPlace_mul, σ.2, τ.2]⟩ = (ρ τ).trans (ρ σ)) ∧
      ∀ σ (c : v.adicCompletion k), ρ σ (localRingHom v w hw c) = localRingHom v w hw c := by
  choose ρ hc _ hx hl using fun σ : {σ : K ≃ₐ[k] K // galPlace σ w = w} =>
    iso_aux σ.1 w w σ.2 v hw hw
  refine ⟨ρ, ?_, fun σ => ⟨hc σ, hx σ⟩, ?_, hl⟩
  · intro σ τ h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply coe_adic_injective w
    show ((σ.1 x : K) : w.adicCompletion K) = ((τ.1 x : K) : w.adicCompletion K)
    rw [← hx σ x, ← hx τ x, h]
  · intro σ τ
    have key := DenseRange.equalizer (denseRange_coe_adic w)
      (g := ρ ⟨σ.1 * τ.1, by rw [galPlace_mul, σ.2, τ.2]⟩) (h := fun y => ρ σ (ρ τ y))
      (hc _) ((hc σ).comp (hc τ)) (by
        funext x
        simp only [Function.comp]
        rw [hx, hx, hx]
        rfl)
    exact RingEquiv.ext (congrFun key)


end NumberFieldKB.WeilBNT
