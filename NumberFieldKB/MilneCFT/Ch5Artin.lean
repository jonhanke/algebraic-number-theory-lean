import NumberFieldKB.MilneCFT.Ch5RayClass
import NumberFieldKB.MilneANT.Ch8
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal
import NumberFieldKB.HilbertClassField.Artin

/-!
# The global Artin map (Milne, *Class Field Theory*, Chapter V, §3, pp. 156–157)

* `idealNorm K L` — the norm $\mathrm{Nm}_{L/K} : I_L \to I_K$ on fractional ideals, $\mathrm{Nm}(\mathfrak P) =
  \mathfrak p^{f(\mathfrak P/\mathfrak p)}$ (Milne p. 157, citing *ANT* p. 68), with the comparison
  `idealNorm_coeIdeal` with Mathlib's `Ideal.relNorm` and `idealNorm_toPrincipalIdeal`
  ($\mathrm{Nm}((\alpha)) = (\mathrm{Nm}\,\alpha)$);
* `artinFrob L v` — the Frobenius element $(\mathfrak p, L/K)$ of an abelian extension (Milne p. 156);
* `artinMap L S` — **the global Artin map** $\psi_{L/K} : I^S \to \mathrm{Gal}(L/K)$,
  $\prod\mathfrak p_i^{n_i} \mapsto \prod(\mathfrak p_i, L/K)^{n_i}$ (p. 156);
* **Example 3.1** (`example_3_1`), **Example 3.2** (`example_3_2`), **Proposition 3.3** (`prop_3_3`),
  **Corollary 3.4** (`cor_3_4`), and the remark after it (`not_injective_after_cor_3_4`).

Abelian extensions are `[IsAbelianGalois K L]`; the commutative group structure on $\mathrm{Gal}(L/K)$ needed for the
products is Mathlib's scoped instance from `IsMulCommutative`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

/-! ## The norm of fractional ideals -/

section IdealNorm

/-- A fractional ideal has nonzero order at only finitely many primes. -/
theorem finite_count_ne_zero {F : Type} [Field F] [NumberField F] (I : FractionalIdeal (𝓞 F)⁰ F) :
    {v : HeightOneSpectrum (𝓞 F) | FractionalIdeal.count F v I ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)

/-- The order at a prime $v$ as a homomorphism from fractional ideal units to $(\mathbb Z, +)$ written
multiplicatively. -/
def countHom {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (FractionalIdeal (𝓞 F)⁰ F)ˣ →* Multiplicative ℤ where
  toFun I := Multiplicative.ofAdd (FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F))
  map_one' := by simp [FractionalIdeal.count_one]
  map_mul' a b := by
    simp [FractionalIdeal.count_mul F v a.ne_zero b.ne_zero]

open Classical in
/-- The order of the prime $v$ at the prime $w$ is $1$ if $v = w$ and $0$ otherwise. -/
theorem count_primeUnitIdeal {F : Type} [Field F] [NumberField F] (v w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((primeUnitIdeal v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      if v = w then 1 else 0 := by
  exact FractionalIdeal.count_maximal F w v

/-- A fractional ideal unit is the product of its prime factors with multiplicity. -/
theorem unit_eq_finprod {F : Type} [Field F] [NumberField F] (a : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    a = ∏ᶠ v : HeightOneSpectrum (𝓞 F), primeUnitIdeal v ^
      FractionalIdeal.count F v (a : FractionalIdeal (𝓞 F)⁰ F) := by
  have h1 : (fun v : HeightOneSpectrum (𝓞 F) => primeUnitIdeal v ^
      FractionalIdeal.count F v (a : FractionalIdeal (𝓞 F)⁰ F)) =
      fun v => QuadFormsKB.Tamagawa.Measure.Weil.primeUnit v ^
      FractionalIdeal.count F v (a : FractionalIdeal (𝓞 F)⁰ F) := rfl
  rw [h1]
  change a = QuadFormsKB.Tamagawa.Measure.Weil.primeProd _
  refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun v => ?_
  rw [QuadFormsKB.Tamagawa.Measure.Weil.count_primeProd _ (finite_count_ne_zero _)]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The prime $\mathfrak p = \mathfrak P \cap \mathcal O_K$ below a prime $\mathfrak P$ of $L$ (QuadFormsKB's
`underPlace`). -/
abbrev primeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  QuadFormsKB.Tamagawa.Measure.Weil.underPlace (k := K) w

/-- The factors of the defining product of `idealNorm` are trivial outside a finite set. -/
theorem idealNorm_mulSupport_finite (c : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    (Function.mulSupport fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnitIdeal (primeBelow K L w) ^
          ((w.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L w (c : FractionalIdeal (𝓞 L)⁰ L))).Finite :=
  (finite_count_ne_zero (c : FractionalIdeal (𝓞 L)⁰ L)).subset fun w hw => by
    simp only [Function.mem_mulSupport, Set.mem_ofPred_eq] at hw ⊢
    intro h0; apply hw; simp [h0]

/-- **The norm of fractional ideals** $\mathrm{Nm}_{L/K} : I_L \to I_K$ (Milne, *CFT*, V, §3, p. 157, recalling
*ANT* p. 68): the homomorphism with $\mathrm{Nm}(\mathfrak P) = \mathfrak p^{f(\mathfrak P/\mathfrak p)}$,
$\mathfrak p = \mathfrak P \cap \mathcal O_K$; on $\mathfrak a = \prod\mathfrak P^{n_\mathfrak P}$ it is
$\prod \mathfrak p^{f(\mathfrak P/\mathfrak p)n_\mathfrak P}$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (the norm map Nm_{L/K} : I_L → I_K)"]
def idealNorm : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun a := ∏ᶠ w : HeightOneSpectrum (𝓞 L), primeUnitIdeal (primeBelow K L w) ^
    ((w.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L w (a : FractionalIdeal (𝓞 L)⁰ L))
  map_one' := by
    simp [FractionalIdeal.count_one]
  map_mul' := by
    intro a b
    have hfin := idealNorm_mulSupport_finite K L
    rw [← finprod_mul_distrib (hfin a) (hfin b)]
    refine finprod_congr fun w => ?_
    rw [Units.val_mul, FractionalIdeal.count_mul L w a.ne_zero b.ne_zero, mul_add, zpow_add]

/-- $\mathrm{Nm}(\mathfrak P) = \mathfrak p^{f(\mathfrak P/\mathfrak p)}$. -/
theorem idealNorm_primeUnitIdeal (w : HeightOneSpectrum (𝓞 L)) :
    idealNorm K L (primeUnitIdeal w) = primeUnitIdeal (primeBelow K L w) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  change ∏ᶠ w' : HeightOneSpectrum (𝓞 L), primeUnitIdeal (primeBelow K L w') ^
    ((w'.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L w' (primeUnitIdeal w : FractionalIdeal (𝓞 L)⁰ L)) = _
  rw [finprod_eq_single _ w]
  · rw [count_primeUnitIdeal]; simp
  · intro w' hw'
    rw [count_primeUnitIdeal]; simp [Ne.symm hw']

/-- On nonzero integral ideals, `idealNorm` is Mathlib's relative norm `Ideal.relNorm`. -/
theorem idealNorm_coeIdeal (I : (Ideal (𝓞 L))⁰) :
    ((idealNorm K L (FractionalIdeal.mk0 L I) : FractionalIdeal (𝓞 K)⁰ K)) =
      ((Ideal.relNorm (𝓞 K) (I : Ideal (𝓞 L)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨J, hJ⟩ := I
  have hJ0 : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
  have key : ∀ J : Ideal (𝓞 L), ∀ hJ0 : J ≠ ⊥,
      ((idealNorm K L (FractionalIdeal.mk0 L ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.relNorm (𝓞 K) J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    intro J
    induction J using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ J hJ =>
      intro h0
      rw [Ideal.isUnit_iff] at hJ
      subst hJ
      have : (FractionalIdeal.mk0 L ⟨⊤, mem_nonZeroDivisors_of_ne_zero h0⟩ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) = 1 :=
        Units.ext (by simp [FractionalIdeal.coe_mk0])
      rw [this, map_one, Ideal.relNorm_top]
      simp
    | h₃ a p ha hp ih =>
      intro h0
      have ha0 : a ≠ ⊥ := fun h => h0 (by simp [h])
      have hp0 : p ≠ ⊥ := hp.ne_zero
      have hmul : (FractionalIdeal.mk0 L ⟨p * a, mem_nonZeroDivisors_of_ne_zero h0⟩ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
          FractionalIdeal.mk0 L ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ *
          FractionalIdeal.mk0 L ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩ :=
        Units.ext (by simp [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_mul])
      rw [hmul, map_mul, Units.val_mul, ih ha0, map_mul, FractionalIdeal.coeIdeal_mul]
      congr 1
      let w : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
      have hw := idealNorm_primeUnitIdeal K L w
      have hmax : w.asIdeal.IsMaximal := w.isMaximal
      have : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
      have hpm : (primeBelow K L w).asIdeal.IsMaximal := (primeBelow K L w).isMaximal
      have := Ideal.relNorm_eq_pow_of_isMaximal (R := 𝓞 K) w.asIdeal (primeBelow K L w).asIdeal
      change ((idealNorm K L (primeUnitIdeal w) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = _
      rw [hw]
      change _ = ((Ideal.relNorm (𝓞 K) w.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [this, FractionalIdeal.coeIdeal_pow]
      rfl
  exact key J hJ0

/-- $\mathrm{Nm}_{L/K}((\alpha)) = (\mathrm{Nm}_{L/K}\alpha)$ (Milne, *CFT*, V, p. 157). -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (Nm((α)) = (Nm α))"]
theorem idealNorm_toPrincipalIdeal (α : Lˣ) :
    idealNorm K L (toPrincipalIdeal (𝓞 L) L α) =
      toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : L →* K) α) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (α : L)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxy
    exact α.ne_zero hxy.symm
  have hyL : (algebraMap (𝓞 L) L y) ≠ 0 := by simpa using hy0
  have hxL : algebraMap (𝓞 L) L x = (α : L) * algebraMap (𝓞 L) L y := by
    rw [← hxy]; field_simp
  -- principal ideals of the integers
  have hspan : ∀ z : 𝓞 L, ∀ hz : z ≠ 0,
      ((idealNorm K L (FractionalIdeal.mk0 L ⟨Ideal.span {z}, mem_nonZeroDivisors_of_ne_zero
          (by simpa using hz)⟩) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (Algebra.norm K (algebraMap (𝓞 L) L z)) := by
    intro z hz
    rw [idealNorm_coeIdeal K L ⟨Ideal.span {z}, mem_nonZeroDivisors_of_ne_zero (by simpa using hz)⟩]
    simp only [Ideal.relNorm_singleton]
    rw [FractionalIdeal.coeIdeal_span_singleton, Algebra.algebraMap_intNorm (L := L)]
  have hnx : Algebra.norm K (algebraMap (𝓞 L) L x) ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; simpa using hx0
  have hny : Algebra.norm K (algebraMap (𝓞 L) L y) ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hyL
  have hmulx : (toPrincipalIdeal (𝓞 L) L α) *
      FractionalIdeal.mk0 L ⟨Ideal.span {y}, mem_nonZeroDivisors_of_ne_zero (by simpa using hy0)⟩ =
      FractionalIdeal.mk0 L ⟨Ideal.span {x}, mem_nonZeroDivisors_of_ne_zero (by simpa using hx0)⟩ := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_span_singleton, ← map_mul, hxL]
  refine mul_right_cancel (b := idealNorm K L (FractionalIdeal.mk0 L ⟨Ideal.span {y},
    mem_nonZeroDivisors_of_ne_zero (by simpa using hy0)⟩)) ?_
  rw [← map_mul, hmulx]
  apply Units.ext
  rw [Units.val_mul, hspan x hx0, hspan y hy0, coe_toPrincipalIdeal,
    ← map_mul, hxL]
  simp [map_mul]

/-- The primes of $L$ above a set $S$ of primes of $K$ (Milne's $S$ for $L$, p. 147). -/
def primesAbove (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  primeBelow K L ⁻¹' S

/-- $\mathrm{Nm}(I_L^S) \subseteq I_K^S$. -/
theorem idealNorm_mem_sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (ha : a ∈ sIdeals (primesAbove K L S)) : idealNorm K L a ∈ sIdeals S := by
  intro v hv
  have key : countHom v (idealNorm K L a) = 1 := by
    change countHom v (∏ᶠ w : HeightOneSpectrum (𝓞 L), primeUnitIdeal (primeBelow K L w) ^
      ((w.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L w (a : FractionalIdeal (𝓞 L)⁰ L))) = 1
    rw [MonoidHom.map_finprod _ (idealNorm_mulSupport_finite K L a)]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    rw [map_zpow]
    by_cases hw : primeBelow K L w = v
    · have : w ∈ primesAbove K L S := by
        show primeBelow K L w ∈ S
        rwa [hw]
      rw [ha w this]; simp
    · have : countHom v (primeUnitIdeal (primeBelow K L w)) = 1 := by
        change Multiplicative.ofAdd _ = 1
        rw [count_primeUnitIdeal]; simp [hw]
      rw [this]; simp
  have := congrArg Multiplicative.toAdd key
  exact this

/-- The norm group $\mathrm{Nm}_{L/K}(I_L^S) \subseteq I_K^S$ (Milne, *CFT*, V, §3, p. 157). -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (the group Nm(I_L^S))"]
def normIdeals (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (sIdeals (primesAbove K L S)).map (idealNorm K L)

theorem normIdeals_le (S : Set (HeightOneSpectrum (𝓞 K))) : normIdeals K L S ≤ sIdeals S := by
  rintro _ ⟨a, ha, rfl⟩
  exact idealNorm_mem_sIdeals K L S a ha

end IdealNorm

/-! ## The Artin map -/

section ArtinMap

open scoped IsMulCommutative

variable {K : Type} [Field K] [NumberField K]
variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The Frobenius element** $(\mathfrak p, L/K)$ of a finite abelian extension (Milne, *CFT*, V, §3, p. 156): for
$\mathfrak p$ unramified in $L$ it is the Frobenius element of any prime above $\mathfrak p$, which does not depend on
the prime (`artinFrob_eq`). (For ramified $\mathfrak p$ the value is meaningless.) -/
@[kb "milne2020cft" "Ch. V, §3, p. 156 (the Frobenius automorphism (p, L/K))"]
def artinFrob (v : HeightOneSpectrum (𝓞 K)) : Gal(L/K) :=
  frobAt K L v (Classical.arbitrary _)

theorem artinFrob_eq (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L)
    (Q : v.asIdeal.primesOver (𝓞 L)) : artinFrob L v = frobAt K L v Q :=
  MilneANT.item_8_14_abelian K L (fun σ τ => mul_comm σ τ) v hv _ Q

/-- The product formula of the Artin map on all fractional ideal units (no condition on the support). -/
def artinTot : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* Gal(L/K) where
  toFun a := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    artinFrob L v ^ FractionalIdeal.count K v (a : FractionalIdeal (𝓞 K)⁰ K)
  map_one' := by
    simp [FractionalIdeal.count_one]
  map_mul' := by
    intro a b
    have hfin : ∀ c : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        artinFrob L v ^ FractionalIdeal.count K v (c : FractionalIdeal (𝓞 K)⁰ K)).Finite :=
      fun c => (finite_count_ne_zero (c : FractionalIdeal (𝓞 K)⁰ K)).subset
        fun w hw => by
          simp only [Function.mem_mulSupport, Set.mem_ofPred_eq] at hw ⊢
          intro h0; apply hw; simp [h0]
    rw [← finprod_mul_distrib (hfin a) (hfin b)]
    refine finprod_congr fun w => ?_
    have := FractionalIdeal.count_mul K w a.ne_zero b.ne_zero
    simp only [Units.val_mul, this, zpow_add]

/-- The Artin map is the restriction of `artinTot`. -/
theorem artinTot_primeUnitIdeal (v : HeightOneSpectrum (𝓞 K)) :
    artinTot L (primeUnitIdeal v) = artinFrob L v := by
  change ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob L w ^
    FractionalIdeal.count K w ((primeUnitIdeal v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [finprod_eq_single _ v]
  · rw [count_primeUnitIdeal]; simp
  · intro w hw
    rw [count_primeUnitIdeal]; simp [Ne.symm hw]

/-- **The global Artin map** (Milne, *CFT*, V, §3, p. 156): for a finite abelian extension $L/K$ and a set $S$ of
primes of $K$ (containing the primes ramified in $L$, for the map to be meaningful),
$\psi_{L/K} : I^S \to \mathrm{Gal}(L/K)$, $\prod\mathfrak p_i^{n_i} \mapsto \prod(\mathfrak p_i, L/K)^{n_i}$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 156 (the global Artin map)"]
def artinMap (S : Set (HeightOneSpectrum (𝓞 K))) : sIdeals S →* Gal(L/K) where
  toFun a := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    artinFrob L v ^ FractionalIdeal.count K v ((a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  map_one' := by
    simp [FractionalIdeal.count_one]
  map_mul' := by
    intro a b
    have hfin : ∀ c : sIdeals S, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        artinFrob L v ^ FractionalIdeal.count K v ((c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)).Finite :=
      fun c => (finite_count_ne_zero ((c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)).subset
        fun w hw => by
          simp only [Function.mem_mulSupport, Set.mem_ofPred_eq] at hw ⊢
          intro h0; apply hw; simp [h0]
    rw [← finprod_mul_distrib (hfin a) (hfin b)]
    refine finprod_congr fun w => ?_
    have := FractionalIdeal.count_mul K w (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero
    simp only [Subgroup.coe_mul, Units.val_mul, this, zpow_add]

/-- The Artin map sends a prime $\mathfrak p \notin S$ to its Frobenius element. -/
theorem artinMap_prime (S : Set (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K))
    (a : sIdeals S) (ha : (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = primeUnitIdeal v) :
    artinMap L S a = artinFrob L v := by
  change artinTot L (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = _
  rw [ha, artinTot_primeUnitIdeal]

/-- If `w` is a prime of `L` whose prime below is unramified, the order of the Frobenius element at that prime is the
residue degree `f(w | p)`. -/
theorem orderOf_artinFrob_primeBelow (w : HeightOneSpectrum (𝓞 L)) (hp : primeBelow K L w ∈ unramifiedPrimes K L) :
    orderOf (artinFrob L (primeBelow K L w)) = w.asIdeal.inertiaDeg (𝓞 K) := by
  have hQ : w.asIdeal ∈ (primeBelow K L w).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [artinFrob_eq L (primeBelow K L w) hp ⟨w.asIdeal, hQ⟩]
  have hmax : w.asIdeal.IsMaximal := w.isMaximal
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hp w.asIdeal w.isPrime ⟨rfl⟩
  have : Finite (𝓞 L ⧸ w.asIdeal) := finite_quotient_of_ne_bot _ w.ne_bot
  exact orderOf_arithFrobAt_nf (K := K) (L := L) w.asIdeal

/-- If `w` is a prime of `L` whose prime below is unramified, then `Frob^f = 1` for `f = f(w | p)`. -/
theorem artinFrob_primeBelow_pow (w : HeightOneSpectrum (𝓞 L)) (hp : primeBelow K L w ∈ unramifiedPrimes K L) :
    artinFrob L (primeBelow K L w) ^ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  rw [← orderOf_artinFrob_primeBelow L w hp]
  exact pow_orderOf_eq_one _

/-- **Frobenius in a tower** for abstract intermediate fields: for `w` a prime of `K'` with unramified image `p` in
`L/K`, the Frobenius of `L/K'` at `w`, restricted to `K`, is the `f(w|p)`-th power of the Frobenius of `L/K` at `p`. -/
theorem artinFrob_restrictScalars_eq_pow (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' L]
    [IsScalarTower K K' L] [IsAbelianGalois K' L] (w : HeightOneSpectrum (𝓞 K'))
    (hp : primeBelow K K' w ∈ unramifiedPrimes K L) :
    (artinFrob (K := K') L w).restrictScalars K =
      artinFrob L (primeBelow K K' w) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  -- every prime of `L` above `w` is unramified over `K'`
  have hunr : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver w.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K') Q := by
    intro Q _ hQo
    have hlies : Q.LiesOver (primeBelow K K' w).asIdeal := by
      refine ⟨?_⟩
      have h1 : Q.under (𝓞 K') = w.asIdeal := (Ideal.LiesOver.over (p := w.asIdeal) (P := Q)).symm
      have h2 := Ideal.under_under (A := 𝓞 K) (B := 𝓞 K') Q
      rw [h1] at h2
      exact h2
    have h2 : Algebra.IsUnramifiedAt (𝓞 K) Q := hp Q ‹_› hlies
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q
    have : Finite (𝓞 L ⧸ Q) := finite_quotient_of_ne_bot Q hne
    exact Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have hw : w ∈ unramifiedPrimes K' L := fun Q hQ hQo => hunr Q
  let Q0 : w.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  have hQ := Q0.2.1
  have hQo := Q0.2.2
  have hlies : Q0.1.LiesOver (primeBelow K K' w).asIdeal := by
    refine ⟨?_⟩
    have h1 : Q0.1.under (𝓞 K') = w.asIdeal := (Ideal.LiesOver.over (p := w.asIdeal) (P := Q0.1)).symm
    have h2 := Ideal.under_under (A := 𝓞 K) (B := 𝓞 K') Q0.1
    rw [h1] at h2
    exact h2
  rw [artinFrob_eq (K := K') L w hw Q0, artinFrob_eq L _ hp ⟨Q0.1, hQ, hlies⟩]
  have hmax : Q0.1.IsMaximal := isMaximal_of_mem_primesOver K' L w Q0
  have : Algebra.IsUnramifiedAt (𝓞 K) Q0.1 := hp Q0.1 hQ hlies
  have : Finite (𝓞 L ⧸ Q0.1) := finite_quotient_of_ne_bot Q0.1 (Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q0.1)
  have key := arithFrobAt_subgroup_eq_pow (A := 𝓞 K) (B := 𝓞 K') (C := 𝓞 L) (G := Gal(L/K))
    (H := Gal(L/K')) (AlgEquiv.restrictScalarsHom K) (fun _ _ => rfl) Q0.1
    (ramificationIdxIn_eq_one_of_isUnramifiedAt Q0.1)
  have hu : Q0.1.under (𝓞 K') = w.asIdeal := (Ideal.LiesOver.over (p := w.asIdeal) (P := Q0.1)).symm
  rw [hu] at key
  exact key

/-- **Example 3.1** (Milne, *CFT*, V, p. 156): for a quadratic field $L = \mathbb Q(\sqrt d)$ ($d$ an integer, not a
square, $s = \sqrt d \in L$) and $S$ a set of primes containing the ramified ones, the Artin map sends an odd prime
$p \notin S$ not dividing $d$ to the automorphism $\sqrt d \mapsto \left(\frac dp\right)\sqrt d$; identifying
$\mathrm{Gal}(L/\mathbb Q)$ with $\{\pm1\}$, $\psi(p) = \left(\frac dp\right)$. (Milne takes $d = m$ square-free and
all unramified $p$; the Legendre symbol needs $p$ odd, as in `MilneANT.example_8_19`.) -/
@[kb "milne2020cft" "Ch. V, Example 3.1"]
theorem example_3_1 (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (hL : Module.finrank ℚ L = 2)
    (d : ℤ) (s : L) (hs : s ^ 2 = d) (hsQ : s ∉ Set.range (algebraMap ℚ L))
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (hvS : v ∉ S)
    (hp2 : MilneANT.ratPrime v ≠ 2) (hpd : ¬ (MilneANT.ratPrime v : ℤ) ∣ d)
    (a : sIdeals S) (ha : (a : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) = primeUnitIdeal v) :
    haveI : Fact (MilneANT.ratPrime v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    artinMap L S a s = (legendreSym (MilneANT.ratPrime v) d : L) * s := by
  have hfact : Fact (MilneANT.ratPrime v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hunr : v ∈ unramifiedPrimes ℚ L := fun Q' hQ' hQo' =>
    MilneANT.isUnramifiedAt_quadratic hL d s hs hsQ v hp2 hpd Q'
  rw [artinMap_prime L S v a ha]
  let Q : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  rw [artinFrob_eq L v hunr Q]
  exact (MilneANT.example_8_19 L hL d s hs hsQ v hp2 hpd Q).1

/-- A rational prime `p` is the generator of a prime `v` of `𝓞 ℚ`, and the principal ideal `(p)` is that prime. -/
theorem exists_prime_toPrincipalIdeal (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), MilneANT.ratPrime v = p ∧
      toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) = primeUnitIdeal v := by
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩
  have hv : Rat.HeightOneSpectrum.natGenerator v = p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)
  refine ⟨v, hv, ?_⟩
  have hI : v.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
    have h1 := Rat.HeightOneSpectrum.span_natGenerator v
    rw [hv] at h1
    ext x
    rw [Ideal.mem_span_singleton, ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
      ← h1, Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change _ = ((v.asIdeal : Ideal (𝓞 ℚ)) : FractionalIdeal (𝓞 ℚ)⁰ ℚ)
  rw [hI, FractionalIdeal.coeIdeal_span_singleton]
  simp

/-- The Artin map on the principal ideal of a positive integer `n` prime to `m` acts on `ζ_m` as `[n]`. -/
theorem autToPow_artinTot_nat (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L] (n : ℕ) :
    ∀ (hn0 : 0 < n) (hn : n.Coprime m),
      (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ
        (artinTot L (toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn0.ne')))) =
      ZMod.unitOfCoprime n hn := by
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    have h1 : Units.mk0 (((1 : ℕ) : ℚ)) (Nat.cast_ne_zero.mpr one_ne_zero) = 1 := by ext; simp
    rw [h1]
    simp only [map_one]
    exact Units.ext (by simp)
  | prime p hp =>
    intro hn0 hn
    obtain ⟨v, hv, htp⟩ := exists_prime_toPrincipalIdeal p hp
    rw [htp, artinTot_primeUnitIdeal]
    have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
    have hnd : ¬ MilneANT.ratPrime v ∣ m := by
      rw [hv]
      intro hd
      have := Nat.eq_one_of_dvd_coprimes hn (dvd_refl p) hd
      exact hp.one_lt.ne' this
    obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
    have h8 := (MilneANT.example_8_18 m L v hnd (Classical.arbitrary _)).1
    have s1 := hζ.autToPow_spec ℚ (artinFrob L v)
    have h8' : artinFrob L v (IsCyclotomicExtension.zeta m ℚ L) = IsCyclotomicExtension.zeta m ℚ L ^ p := by
      rw [← hv]; exact h8
    rw [h8'] at s1
    have := MilneANT.natCast_eq_of_zeta_pow_eq hζ s1
    rw [ZMod.natCast_zmod_val] at this
    exact Units.ext (by rw [this]; simp)
  | mul a b iha ihb =>
    intro hn0 hn
    have ha0 : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hb0 : 0 < b := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hna : a.Coprime m := Nat.Coprime.coprime_mul_right hn
    have hnb : b.Coprime m := Nat.Coprime.coprime_mul_left hn
    have : Units.mk0 (((a * b : ℕ)) : ℚ) (Nat.cast_ne_zero.mpr hn0.ne') =
        Units.mk0 (a : ℚ) (Nat.cast_ne_zero.mpr ha0.ne') * Units.mk0 (b : ℚ) (Nat.cast_ne_zero.mpr hb0.ne') := by
      ext; simp
    rw [this, map_mul, map_mul, map_mul, iha ha0 hna, ihb hb0 hnb]
    exact Units.ext (by simp)

/-- **Example 3.2** (Milne, *CFT*, V, p. 157): for $L = \mathbb Q(\zeta_m)$ and $S$ the primes dividing $m$, the Artin
map $I^S \to \mathrm{Gal}(L/\mathbb Q)$ is the composite of $(r/s) \mapsto [r][s]^{-1} \in (\mathbb Z/m\mathbb Z)^\times$
($r, s$ positive integers prime to $m$) and $[n] \mapsto (\zeta \mapsto \zeta^n)$; here: the automorphism
$\psi((r/s))$ acts on $\zeta_m$ as $[r][s]^{-1}$ (Mathlib's `IsPrimitiveRoot.autToPow`). Milne assumes $m$ odd or
divisible by $4$, so that $S$ is exactly the set of ramified primes; the statement holds for all $m \ge 1$. -/
@[kb "milne2020cft" "Ch. V, Example 3.2"]
theorem example_3_2 (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [IsAbelianGalois ℚ L] (r s : ℕ) (hr : r.Coprime m) (hs : s.Coprime m) (hr0 : 0 < r) (hs0 : 0 < s)
    (a : sIdeals {v : HeightOneSpectrum (𝓞 ℚ) | MilneANT.ratPrime v ∣ m})
    (ha : (a : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) =
      toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 ((r : ℚ) / s) (by positivity))) :
    (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ
        (artinMap L {v : HeightOneSpectrum (𝓞 ℚ) | MilneANT.ratPrime v ∣ m} a) =
      ZMod.unitOfCoprime r hr * (ZMod.unitOfCoprime s hs)⁻¹ := by
  show (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ (artinTot L (a : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ)) = _
  have hsplit : Units.mk0 ((r : ℚ) / s) (by positivity) =
      Units.mk0 (r : ℚ) (Nat.cast_ne_zero.mpr hr0.ne') * (Units.mk0 (s : ℚ) (Nat.cast_ne_zero.mpr hs0.ne'))⁻¹ := by
    ext; simp [div_eq_mul_inv]
  rw [ha, hsplit, map_mul, map_inv, map_mul, map_inv, map_mul, map_inv,
    autToPow_artinTot_nat m L r hr0 hr, autToPow_artinTot_nat m L s hs0 hs]

/-- **Proposition 3.3** (Milne, *CFT*, V, p. 157): for $K \subseteq K' \subseteq L$ with $L/K$ finite abelian and $S$ a
set of primes of $K$ containing those ramified in $L$, the diagram
$I_{K'}^{S} \xrightarrow{\psi_{L/K'}} \mathrm{Gal}(L/K')$, $I_K^S \xrightarrow{\psi_{L/K}} \mathrm{Gal}(L/K)$ with
vertical maps $\mathrm{Nm}_{K'/K}$ and the inclusion commutes:
$\psi_{L/K}(\mathrm{Nm}_{K'/K}\mathfrak a) = \psi_{L/K'}(\mathfrak a)$. ($S$ for $K'$ is the set of primes above $S$;
$L/K'$ is abelian, `IsAbelianGalois.tower_top`.) -/
@[kb "milne2020cft" "Ch. V, Proposition 3.3"]
theorem prop_3_3 (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]
    [IsAbelianGalois K' L] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v, v ∉ S → v ∈ unramifiedPrimes K L) (a : sIdeals (primesAbove K K' S)) (b : sIdeals S)
    (hb : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = idealNorm K K' a) :
    (artinMap L (primesAbove K K' S) a).restrictScalars K = artinMap L S b := by
  change (AlgEquiv.restrictScalarsHom K) (artinTot (K := K') L (a : (FractionalIdeal (𝓞 K')⁰ K')ˣ)) =
    artinTot L (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  rw [hb]
  have hcl : (a : (FractionalIdeal (𝓞 K')⁰ K')ˣ) ∈
      Subgroup.closure (primeUnitIdeal '' (primesAbove K K' S)ᶜ) := by
    rw [← sIdeals_eq_closure]; exact a.2
  refine MonoidHom.eqOn_closure (f := (AlgEquiv.restrictScalarsHom K).comp (artinTot (K := K') L))
    (g := (artinTot (K := K) L).comp (idealNorm K K')) ?_ hcl
  rintro _ ⟨w, hw, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [artinTot_primeUnitIdeal, idealNorm_primeUnitIdeal, map_pow, artinTot_primeUnitIdeal]
  exact artinFrob_restrictScalars_eq_pow L K' w (hS _ hw)

/-- **Corollary 3.4** (Milne, *CFT*, V, p. 157): for a finite abelian extension $L/K$ and $S$ containing the ramified
primes, $\mathrm{Nm}_{L/K}(I_L^S)$ is contained in the kernel of $\psi_{L/K} : I^S \to \mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. V, Corollary 3.4"]
theorem cor_3_4 (S : Set (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, v ∉ S → v ∈ unramifiedPrimes K L)
    (b : sIdeals S) (hb : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ normIdeals K L S) :
    artinMap L S b = 1 := by
  obtain ⟨a, ha, hab⟩ := hb
  change artinTot L (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1
  rw [← hab]
  have hcl : a ∈ Subgroup.closure (primeUnitIdeal '' (primesAbove K L S)ᶜ) := by
    rw [← sIdeals_eq_closure]; exact ha
  refine MonoidHom.eqOn_closure (f := (artinTot (K := K) L).comp (idealNorm K L)) (g := 1) ?_ hcl
  rintro _ ⟨w, hw, rfl⟩
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
  rw [idealNorm_primeUnitIdeal, map_pow, artinTot_primeUnitIdeal]
  exact artinFrob_primeBelow_pow L w (hS _ hw)

/-- At an unramified prime `p`, the order at `p` of a norm is divisible by the order of the Frobenius element
(the residue degree of every prime above `p`). -/
theorem dvd_count_idealNorm (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ unramifiedPrimes K L)
    (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    (orderOf (artinFrob L p) : ℤ) ∣ Multiplicative.toAdd (countHom p (idealNorm K L a)) := by
  classical
  change _ ∣ Multiplicative.toAdd (countHom p (∏ᶠ w : HeightOneSpectrum (𝓞 L), primeUnitIdeal (primeBelow K L w) ^
      ((w.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L w (a : FractionalIdeal (𝓞 L)⁰ L))))
  rw [MonoidHom.map_finprod _ (idealNorm_mulSupport_finite K L a)]
  refine finprod_induction (fun x : Multiplicative ℤ => (orderOf (artinFrob L p) : ℤ) ∣ Multiplicative.toAdd x)
    ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simpa [toAdd_mul] using dvd_add hx hy
  · intro w
    rw [map_zpow]
    by_cases hw : primeBelow K L w = p
    · subst hw
      have h1 : Multiplicative.toAdd (countHom (primeBelow K L w) (primeUnitIdeal (primeBelow K L w))) = 1 := by
        change FractionalIdeal.count K (primeBelow K L w) _ = 1
        rw [count_primeUnitIdeal]; simp
      rw [toAdd_zpow, h1, smul_eq_mul, mul_one, ← orderOf_artinFrob_primeBelow L w hp]
      exact Dvd.intro _ rfl
    · have h1 : Multiplicative.toAdd (countHom p (primeUnitIdeal (primeBelow K L w))) = 0 := by
        change FractionalIdeal.count K p _ = 0
        rw [count_primeUnitIdeal]; simp [hw]
      rw [toAdd_zpow, h1]; simp

/-- **After Corollary 3.4** (Milne, *CFT*, V, p. 157): if $L \ne K$ the group $I^S/\mathrm{Nm}(I_L^S)$ is infinite
(infinitely many primes do not split), so the map $I^S/\mathrm{Nm}(I_L^S) \to \mathrm{Gal}(L/K)$ induced by the Artin
map is not injective. (Milne does not exclude $L = K$, where the quotient is trivial.) -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (I^S/Nm(I_L^S) is infinite)"]
theorem not_injective_after_cor_3_4 (hL : 1 < Module.finrank K L) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) :
    ((normIdeals K L S).subgroupOf (sIdeals S)).index = 0 := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(L/K), σ ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton Gal(L/K) := ⟨fun x y => (h x).trans (h y).symm⟩
    have h1 : Nat.card Gal(L/K) = 1 := Nat.card_of_subsingleton 1
    rw [IsGalois.card_aut_eq_finrank K L] at h1
    omega
  set T : Set (HeightOneSpectrum (𝓞 K)) := {𝔭 : HeightOneSpectrum (𝓞 K) |
      𝔭 ∈ unramifiedPrimes K L ∧ ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), frobAt K L 𝔭 Q = σ} \ S with hTdef
  have hT : T.Infinite := (NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite K L σ).sdiff hS
  -- the class of the prime `𝔭 ∉ S`
  let e : T → (sIdeals S ⧸ (normIdeals K L S).subgroupOf (sIdeals S)) := fun 𝔭 =>
    QuotientGroup.mk ⟨primeUnitIdeal 𝔭.1, fun v hv => by
      rw [count_primeUnitIdeal]
      have : 𝔭.1 ≠ v := fun h => 𝔭.2.2 (h ▸ hv)
      simp [this]⟩
  have hinj : Function.Injective e := by
    intro p q hpq
    by_contra hne
    have hne' : p.1 ≠ q.1 := fun h => hne (Subtype.ext h)
    have hmem := QuotientGroup.eq.mp hpq
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨-, Q, hQ⟩ := p.2.1
    have hord : 2 ≤ orderOf (artinFrob L p.1) := by
      rw [artinFrob_eq L p.1 p.2.1.1 Q, hQ]
      have hpos : 0 < orderOf σ := orderOf_pos σ
      have : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
      omega
    have hd := dvd_count_idealNorm L p.1 p.2.1.1 a
    rw [ha] at hd
    have hc : Multiplicative.toAdd (countHom p.1 (((primeUnitIdeal p.1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))⁻¹ *
        primeUnitIdeal q.1)) = -1 := by
      have h1 : Multiplicative.toAdd (countHom p.1 (primeUnitIdeal p.1)) = 1 := by
        change FractionalIdeal.count K p.1 _ = 1
        rw [count_primeUnitIdeal]; simp
      have h2 : Multiplicative.toAdd (countHom p.1 (primeUnitIdeal q.1)) = 0 := by
        change FractionalIdeal.count K p.1 _ = 0
        rw [count_primeUnitIdeal]; simp [Ne.symm hne']
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, h2]; norm_num
    change _ ∣ Multiplicative.toAdd (countHom p.1 ((primeUnitIdeal p.1)⁻¹ * primeUnitIdeal q.1)) at hd
    rw [hc] at hd
    have := Int.le_of_dvd (by norm_num) ((dvd_neg).mp hd)
    omega
  have : Infinite T := hT.to_subtype
  have := Infinite.of_injective e hinj
  exact Nat.card_eq_zero_of_infinite

end ArtinMap

end NumberFieldKB.MilneCFT
