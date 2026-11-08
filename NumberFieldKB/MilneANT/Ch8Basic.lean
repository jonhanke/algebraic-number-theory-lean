import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.Chebotarev.Unconditional

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: definitions

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

* **Normalized absolute value of a place** (prose definition, p. 137; `normAbv`): the usual absolute value at a real
  place, its square at a complex place, $N(\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}}$ at a finite place. Places
  are Mathlib's `FinitePlace K ⊕ InfinitePlace K` (as in the Chapter 7 files).
* **Galois action on absolute values** (prose definition, p. 139; `conjAbv`): $|\alpha|_{\sigma w} = |\sigma^{-1}\alpha|_w$,
  and the **decomposition group of an absolute value** (prose definition, p. 139; `decompGroupAbv`), its stabilizer.
  Comparison lemmas: on finite places the action is the action on prime ideals (`conjAbv_finitePlace`), so the
  decomposition group is Mathlib's stabilizer of the prime ideal (`decompGroupAbv_finitePlace`); on infinite places it
  is Mathlib's action on `InfinitePlace` (`conjAbv_infinitePlace`).
* **Definition 8.30** (`HasNaturalDensity`): natural density of a set of finite primes.
* **$\mathrm{Spl}(L/K)$ and $\mathrm{Spl}'(L/K)$** (prose definitions, p. 149): the primes splitting completely
  (the library's `NumberFieldKB.Chebotarev.splitPrimes`, tagged here) and the primes with at least one split factor
  (`splitPrimes'`); $\mathrm{Spl}\subseteq\mathrm{Spl}'$ with equality for Galois extensions.
-/

open NumberField IsDedekindDomain Filter Topology
open scoped Pointwise

namespace NumberFieldKB.MilneANT

noncomputable section

/-! ## Normalized absolute values -/

section Normalized

variable (K : Type*) [Field K] [NumberField K]

/-- **The normalized absolute value of a place** (prose definition, Milne p. 137): at a finite place
$\mathfrak p$ it is $\lVert x\rVert_{\mathfrak p} = N(\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}(x)}$ (Mathlib's
`FinitePlace` is already normalized this way, `normAbv_finitePlace_mul_absNorm_pow`); at an infinite place $w$ it is
$|x|_w^{m_w}$ with $m_w = 1$ for a real place and $m_w = 2$ for a complex place (Mathlib's `InfinitePlace.mult`), i.e.
the usual absolute value on $\mathbb R$ and its square on $\mathbb C$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, the normalized absolute value of a place, p. 137"]
def normAbv : FinitePlace K ⊕ InfinitePlace K → K → ℝ
  | .inl w => fun x => w x
  | .inr w => fun x => w x ^ w.mult

@[simp] theorem normAbv_inl (w : FinitePlace K) (x : K) : normAbv K (.inl w) x = w x := rfl

@[simp] theorem normAbv_inr (w : InfinitePlace K) (x : K) : normAbv K (.inr w) x = w x ^ w.mult := rfl

/-- At a finite place the normalized absolute value is $N(\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}}$:
$\lVert x\rVert_{\mathfrak p}\cdot N(\mathfrak p)^{\operatorname{ord}_{\mathfrak p}(x)} = 1$ for a nonzero integer $x$
(from Mathlib's `HeightOneSpectrum.embedding_mul_absNorm`). -/
theorem normAbv_finitePlace_mul_absNorm_pow (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) :
    normAbv K (.inl (FinitePlace.mk v)) (x : K) *
      (Ideal.absNorm v.asIdeal : ℝ) ^ multiplicity v.asIdeal (Ideal.span {x}) = 1 := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have h := HeightOneSpectrum.embedding_mul_absNorm K v hx
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, Nat.cast_pow] at h
  simpa using h

end Normalized

/-! ## The Galois action on absolute values; decomposition groups -/

section GaloisAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The conjugate absolute value** $\sigma w$ (prose definition, Milne p. 139): $|\alpha|_{\sigma w} =
|\sigma^{-1}\alpha|_w$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, the Galois action on primes, p. 139"]
def conjAbv (σ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := (σ.symm : L ≃+* L).toRingHom) σ.symm.injective

@[simp] theorem conjAbv_apply (σ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) (x : L) :
    conjAbv σ w x = w (σ.symm x) := rfl

@[simp] theorem conjAbv_one (w : AbsoluteValue L ℝ) : conjAbv (1 : L ≃ₐ[K] L) w = w := by
  ext x; rfl

theorem conjAbv_mul (σ τ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) :
    conjAbv (σ * τ) w = conjAbv σ (conjAbv τ w) := by
  ext x; rfl

/-- The Galois action on absolute values (`conjAbv`) as a `MulAction` (a definition, not an instance, to avoid
clashing with other actions). -/
@[instance_reducible]
def conjAbvAction : MulAction (L ≃ₐ[K] L) (AbsoluteValue L ℝ) where
  smul := conjAbv
  one_smul := conjAbv_one
  mul_smul := conjAbv_mul

/-- **The decomposition (splitting) group of an absolute value** (prose definition, Milne p. 139):
$G_w = \{\sigma \in G \mid \sigma w = w\}$, the stabilizer of $w$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, the decomposition group of a prime, p. 139"]
def decompGroupAbv (w : AbsoluteValue L ℝ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | conjAbv σ w = w}
  one_mem' := conjAbv_one w
  mul_mem' {σ τ} hσ hτ := by
    change conjAbv (σ * τ) w = w
    rw [conjAbv_mul]
    rw [Set.mem_ofPred_eq] at hσ hτ
    rw [hτ, hσ]
  inv_mem' {σ} hσ := by
    change conjAbv σ⁻¹ w = w
    rw [Set.mem_ofPred_eq] at hσ
    conv_lhs => rw [← hσ]
    rw [← conjAbv_mul, inv_mul_cancel, conjAbv_one]

/-- Milne p. 139: $G_{\tau w} = \tau G_w \tau^{-1}$. -/
theorem decompGroupAbv_conj (τ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ decompGroupAbv (conjAbv τ w) ↔ τ⁻¹ * σ * τ ∈ decompGroupAbv (K := K) w := by
  change conjAbv σ (conjAbv τ w) = conjAbv τ w ↔ conjAbv (τ⁻¹ * σ * τ) w = w
  rw [mul_assoc, conjAbv_mul, conjAbv_mul]
  constructor
  · intro h
    rw [h, ← conjAbv_mul, inv_mul_cancel, conjAbv_one]
  · intro h
    have h2 := congrArg (conjAbv (K := K) τ) h
    rw [← conjAbv_mul, mul_inv_cancel, conjAbv_one] at h2
    exact h2

end GaloisAction

section NumberFieldAction

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- **Comparison with Mathlib, infinite places**: `conjAbv` agrees with Mathlib's action of $\mathrm{Gal}(L/K)$ on
`InfinitePlace L` ($(\sigma w)(x) = w(\sigma^{-1}x)$). -/
theorem conjAbv_infinitePlace (σ : Gal(L/K)) (w : InfinitePlace L) : conjAbv σ w.1 = (σ • w).1 := by
  ext x; rfl

/-- The Galois action on ideals of `𝓞 L` preserves the absolute norm. -/
theorem absNorm_smul_ideal (σ : Gal(L/K)) (I : Ideal (𝓞 L)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

omit [NumberField L] in
/-- The Galois action on ideals of `𝓞 L` preserves multiplicities. -/
theorem multiplicity_smul_ideal (σ : Gal(L/K)) (P I : Ideal (𝓞 L)) :
    multiplicity (σ • P) (σ • I) = multiplicity P I := by
  have := multiplicity_map_eq (MulDistribMulAction.toMulEquiv (Ideal (𝓞 L)) σ) (a := P) (b := I)
  simpa using this

omit [NumberField L] in
/-- The Galois action on ideals of `𝓞 L` sends the principal ideal of `a` to that of `σ a`. -/
theorem span_singleton_smul (σ : Gal(L/K)) (a : 𝓞 L) :
    Ideal.span {σ • a} = σ • Ideal.span {a} := by
  simp [Ideal.pointwise_smul_def, Ideal.map_span]

/-- Integral case of `conjAbv_finitePlace`: $|\sigma^{-1}a|_{\mathfrak P} = |a|_{\sigma\mathfrak P}$ for
$a \in \mathcal O_L$. -/
theorem conjAbv_finitePlace_int [NumberField K] (σ : Gal(L/K)) (P Q : HeightOneSpectrum (𝓞 L))
    (hQ : Q.asIdeal = σ • P.asIdeal) (a : 𝓞 L) :
    (FinitePlace.mk P).1 (σ.symm (a : L)) = (FinitePlace.mk Q).1 (a : L) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hb0 : σ⁻¹ • a ≠ 0 := by
    intro h
    apply ha0
    have := congrArg (fun y => σ • y) h
    simpa [smul_smul] using this
  have hb := normAbv_finitePlace_mul_absNorm_pow L P hb0
  have ha := normAbv_finitePlace_mul_absNorm_pow L Q ha0
  have hm : multiplicity P.asIdeal (Ideal.span {σ⁻¹ • a}) = multiplicity Q.asIdeal (Ideal.span {a}) := by
    rw [hQ, span_singleton_smul, ← multiplicity_smul_ideal K L σ P.asIdeal (σ⁻¹ • Ideal.span {a}), smul_inv_smul]
  have hN : Ideal.absNorm Q.asIdeal = Ideal.absNorm P.asIdeal := by
    rw [hQ, absNorm_smul_ideal]
  rw [hm] at hb
  rw [hN] at ha
  have hpos : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) ^ multiplicity Q.asIdeal (Ideal.span {a}) := by
    have : 0 < Ideal.absNorm P.asIdeal := Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩)
    positivity
  have key := hb.trans ha.symm
  have e : normAbv L (.inl (FinitePlace.mk P)) ((σ⁻¹ • a : 𝓞 L) : L) =
      normAbv L (.inl (FinitePlace.mk Q)) (a : L) := mul_right_cancel₀ hpos.ne' key
  exact e

/-- **Comparison with Mathlib, finite places**: the conjugate of the $\mathfrak P$-adic absolute value is the
$\sigma\mathfrak P$-adic absolute value, as in Milne p. 139 ("if $w$ is defined by $\mathfrak P$ then $\sigma w$ is
defined by $\sigma\mathfrak P$"). -/
theorem conjAbv_finitePlace [NumberField K] (σ : Gal(L/K)) (P : HeightOneSpectrum (𝓞 L)) :
    ∃ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal = σ • P.asIdeal ∧
      conjAbv σ (FinitePlace.mk P).1 = (FinitePlace.mk Q).1 := by
  have hne : σ • P.asIdeal ≠ ⊥ := by
    intro h
    apply P.ne_bot
    have := congrArg (fun J => σ⁻¹ • J) h
    simpa [smul_smul] using this
  have := P.isPrime
  let Q : HeightOneSpectrum (𝓞 L) := ⟨σ • P.asIdeal, Ideal.IsPrime.smul σ, hne⟩
  refine ⟨Q, rfl, ?_⟩
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have h1 := conjAbv_finitePlace_int K L σ P Q rfl a
  have h2 := conjAbv_finitePlace_int K L σ P Q rfl b
  rw [conjAbv_apply, map_div₀ σ.symm]
  change (FinitePlace.mk P) (σ.symm (a : L) / σ.symm (b : L)) = (FinitePlace.mk Q) ((a : L) / (b : L))
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) h1 h2

/-- **Comparison with Mathlib, decomposition groups** (prose definition, Milne p. 139): the decomposition group of the
$\mathfrak P$-adic absolute value is the stabilizer of $\mathfrak P$ (Mathlib's `MulAction.stabilizer`, the
decomposition group $D(\mathfrak P)$ used by `IsDecompositionField`). -/
theorem decompGroupAbv_finitePlace [NumberField K] (P : HeightOneSpectrum (𝓞 L)) :
    decompGroupAbv (K := K) (FinitePlace.mk P).1 = MulAction.stabilizer Gal(L/K) P.asIdeal := by
  ext σ
  obtain ⟨Q, hQ, hc⟩ := conjAbv_finitePlace K L σ P
  rw [MulAction.mem_stabilizer_iff, ← hQ]
  change conjAbv σ (FinitePlace.mk P).1 = (FinitePlace.mk P).1 ↔ _
  rw [hc]
  constructor
  · intro h
    have : FinitePlace.mk Q = FinitePlace.mk P := Subtype.ext h
    rw [FinitePlace.mk_eq_iff] at this
    rw [this]
  · intro h
    have : Q = P := HeightOneSpectrum.ext h
    rw [this]

end NumberFieldAction

/-! ## Definition 8.30: natural density -/

section Density

variable {K : Type*} [Field K] [NumberField K]

/-- The number of nonzero prime ideals of `𝓞 K` in `S` of norm at most `x`. -/
def primeCount (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℕ :=
  {𝔭 ∈ S | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x}.ncard

/-- **Definition 8.30 (natural density).** A set $S$ of finite primes of $K$ has natural density $\delta$ if
$$\lim_{N\to\infty}\frac{|\{\mathfrak p\in S : N\mathfrak p\le N\}|}{|\{\mathfrak p : N\mathfrak p\le N\}|} = \delta.$$
Primes are the nonzero prime ideals of `𝓞 K` (`HeightOneSpectrum`), as in Mathlib's Dirichlet density
`NumberField.Set.HasDirichletDensity`. -/
@[kb "milne2020ant" "v3.08, Def. 8.30, p. 147"]
def HasNaturalDensity (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => (primeCount S x : ℝ) / primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x)
    atTop (𝓝 δ)

/-- Finitely many primes have norm at most `x` (so the counts in Definition 8.30 are finite). -/
theorem finite_setOf_absNorm_le (x : ℝ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x}.Finite := by
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊x⌋₊).preimage
    (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal)
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  intro 𝔭 h𝔭
  exact Nat.le_floor h𝔭

/-- There are infinitely many nonzero prime ideals of `𝓞 K` (each rational prime lies below one, and distinct
rational primes lie below distinct ones). -/
theorem infinite_heightOneSpectrum : (Set.univ : Set (HeightOneSpectrum (𝓞 K))).Infinite := by
  have key : ∀ p : Nat.Primes, ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
    intro p
    have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := by
      have : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
      exact (Ideal.span_singleton_prime this.ne_zero |>.mpr this).isMaximal (by simpa using this.ne_zero)
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)}) (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        have : x = 0 := by simpa using hx
        simp [this])
    have hmem : ((p : ℕ) : 𝓞 K) ∈ Q := by
      have : ((p : ℕ) : ℤ) ∈ Ideal.span {((p : ℕ) : ℤ)} := Ideal.mem_span_singleton_self _
      have h2 := hl.symm
      rw [Ideal.under_def] at h2
      rw [h2] at this
      simpa using this
    refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
    intro h
    rw [h] at hmem
    have : ((p : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact p.2.ne_zero (by exact_mod_cast this)
  choose f hf using key
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ (fun _ => Set.mem_univ _)
  intro p q hpq
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).mpr (fun h => hne (Subtype.ext h))
  have hc' : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨a, b, hab⟩ := hc'
  have h1 : (1 : 𝓞 K) ∈ (f p).asIdeal := by
    have e : (1 : 𝓞 K) = (a : 𝓞 K) * ((p : ℕ) : 𝓞 K) + (b : 𝓞 K) * ((q : ℕ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hab
      push_cast at this
      exact this.symm
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hf p)) (Ideal.mul_mem_left _ _ ?_)
    rw [hpq]; exact hf q
  exact (f p).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The prime count is monotone in `x`. -/
theorem primeCount_univ_mono : Monotone (fun x : ℝ => primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) := by
  intro x y hxy
  unfold primeCount
  refine Set.ncard_le_ncard ?_
    ((finite_setOf_absNorm_le y).subset (fun 𝔭 h => h.2))
  intro 𝔭 h𝔭
  exact ⟨h𝔭.1, h𝔭.2.trans hxy⟩

/-- The number of primes of norm at most `x` tends to infinity. -/
theorem tendsto_primeCount_univ : Tendsto (fun x : ℝ => (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x))
    atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone primeCount_univ_mono ?_
  intro n
  obtain ⟨T, -, hTfin, hT⟩ := (infinite_heightOneSpectrum (K := K)).exists_subset_ncard_eq n
  obtain ⟨x, hx⟩ := (hTfin.image (fun 𝔭 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔭.asIdeal : ℝ))).bddAbove
  refine ⟨x, ?_⟩
  unfold primeCount
  rw [← hT]
  exact Set.ncard_le_ncard (fun 𝔭 h𝔭 => ⟨Set.mem_univ _, hx ⟨𝔭, h𝔭, rfl⟩⟩)
    ((finite_setOf_absNorm_le x).subset (fun 𝔭 h => h.2))

/-- A finite set of primes has natural density $0$. -/
theorem hasNaturalDensity_zero_of_finite {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    HasNaturalDensity S 0 := by
  unfold HasNaturalDensity
  have hd : Tendsto (fun x : ℝ => (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_primeCount_univ
  have h0 : Tendsto (fun x : ℝ => (S.ncard : ℝ) / primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) h0
  have hle : primeCount S x ≤ S.ncard :=
    Set.ncard_le_ncard (fun 𝔭 (h𝔭 : 𝔭 ∈ {𝔭 ∈ S | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x}) => h𝔭.1) hS
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)

/-- The natural density is unique. -/
theorem HasNaturalDensity.unique {S : Set (HeightOneSpectrum (𝓞 K))} {δ δ' : ℝ} (h : HasNaturalDensity S δ)
    (h' : HasNaturalDensity S δ') : δ = δ' := by
  unfold HasNaturalDensity at h h'
  exact tendsto_nhds_unique h h'

end Density

/-! ## Split primes: $\mathrm{Spl}(L/K)$ and $\mathrm{Spl}'(L/K)$ -/

section Split

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- Prose definition (p. 149): $\mathrm{Spl}(L/K)$, the primes of $K$ that split completely in $L$ (every prime above
-- has $e = f = 1$). The library's definition, from the Chebotarev formalization.
attribute [kb "milne2020ant" "v3.08, Ch. 8, the set Spl(L/K) of primes splitting completely, p. 149"]
  NumberFieldKB.Chebotarev.splitPrimes

/-- **$\mathrm{Spl}'(L/K)$** (prose definition, Milne p. 149): the primes of $K$ having at least one split factor in
$L$, i.e. some prime $\mathfrak P$ above $\mathfrak p$ with $e(\mathfrak P/\mathfrak p) = f(\mathfrak P/\mathfrak p) = 1$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, the set Spl'(L/K) of primes with a split factor, p. 149"]
def splitPrimes' : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L),
    Q.1.ramificationIdx (𝓞 K) = 1 ∧ Q.1.inertiaDeg (𝓞 K) = 1}

/-- Milne p. 149: $\mathrm{Spl}(L/K) \subseteq \mathrm{Spl}'(L/K)$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, Spl(L/K) ⊆ Spl'(L/K), p. 149"]
theorem splitPrimes_subset_splitPrimes' :
    NumberFieldKB.Chebotarev.splitPrimes K L ⊆ splitPrimes' K L := by
  intro 𝔭 h𝔭
  have := 𝔭.isPrime
  obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)))
  exact ⟨Q, h𝔭 Q⟩

/-- Milne p. 149: $\mathrm{Spl}(L/K) = \mathrm{Spl}'(L/K)$ when $L/K$ is Galois. -/
@[kb "milne2020ant" "v3.08, Ch. 8, Spl(L/K) = Spl'(L/K) for Galois L/K, p. 149"]
theorem splitPrimes_eq_splitPrimes' [IsGalois K L] :
    NumberFieldKB.Chebotarev.splitPrimes K L = splitPrimes' K L := by
  refine Set.Subset.antisymm (splitPrimes_subset_splitPrimes' K L) ?_
  rintro 𝔭 ⟨Q₀, he, hf⟩ Q
  have := 𝔭.isPrime
  have := Q₀.2.1
  have := Q₀.2.2
  have := Q.2.1
  have := Q.2.2
  exact ⟨(Ideal.ramificationIdx_eq_of_isGaloisGroup 𝔭.asIdeal Q.1 Q₀.1 Gal(L/K)).trans he,
    (Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal Q.1 Q₀.1 Gal(L/K)).trans hf⟩

end Split

end

end NumberFieldKB.MilneANT
