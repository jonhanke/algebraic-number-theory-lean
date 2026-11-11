import NumberFieldKB.MilneCFT.Ch8.Reciprocity
import NumberFieldKB.MilneCFT.Ch5IdelicMain
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VIII §5: the Hilbert symbol and the power reciprocity law

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §5,
printed pp. 245–248 (printed page = pdf page − 9). See `Reciprocity.lean` for the power residue symbol and for the
definition of the Hilbert symbol used here (the formula of Remark 5.9 with the local components of an idèlic Artin
map).

* **5.5** (`item_5_5`): conditional on Chapter V's `ReciprocityLaw`.
* `hilbertArtin`, `hilbertArtinInf`: the Hilbert symbol $(a,b)_v$ of order $n$.
* **5.8** (`item_5_8`), **5.10** (`item_5_10`, product formula): proved for an idèlic Artin map (trivial on
  $K^\times$ for 5.10).
* **5.7** (`Item5_7`): statement, with Milne's hypothesis $\zeta_n \in K$; proved in `Item57Uncond.lean`. The
  form without that hypothesis is `Item5_7NoRoot` (false, `Item57Counter.lean`).
* **Theorem 5.11** (`theorem_5_11`): the power reciprocity law, from 5.7, 5.8, 5.10 (unconditional form
  `theorem_5_11_uncond` in `Item57Uncond.lean`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.MilneCFT
open scoped nonZeroDivisors IsMulCommutative

set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- A Galois automorphism is determined by its value on a generator. -/
theorem gal_ext_of_gen {L : Type} [Field L] [NumberField L] [Algebra K L] {α : L}
    (hgen : IntermediateField.adjoin K {α} = ⊤) {σ τ : Gal(L/K)} (h : σ α = τ α) : σ = τ := by
  have hgen' : Algebra.adjoin K {α} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := K)
      (IsAlgebraic.of_finite K α)
    rw [hgen] at this
    simpa using this.symm
  exact AlgEquiv.coe_toAlgHom_injective (AlgHom.ext_of_adjoin_eq_top hgen' (by simpa using h))

/-- **5.5** (Milne, *CFT*, VIII, 5.5, p. 245; conditional on Chapter V's named reciprocity law `ReciprocityLaw`):
for $a \in K^\times$ there is a modulus $\mathfrak m$ with support in $S(a)$ such that $(a/\mathfrak b)$ depends only
on the class of $\mathfrak b$ in the ray class group $C_\mathfrak m$. -/
@[kb "milne2020cft" "Ch. VIII, 5.5, p. 245"]
theorem item_5_5 (hR : ReciprocityLaw K) (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (ha : a ≠ 0) : ∃ m : Modulus K, m.finiteSupport ⊆ Sset n {a} ∧
      ∀ b b' : (FractionalIdeal (𝓞 K)⁰ K)ˣ, b ∈ sIdeals (Sset n {a}) → b' ∈ sIdeals (Sset n {a}) →
        b * b'⁻¹ ∈ rayPrincipal m → powerResidueIdeal n a b = powerResidueIdeal n a b' := by
  classical
  have hcastK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set p : Polynomial K := Polynomial.X ^ n - Polynomial.C a with hp
  have hsep : p.Separable := Polynomial.separable_X_pow_sub_C a hcastK ha
  have : NumberField p.SplittingField := NumberField.of_module_finite K p.SplittingField
  have : IsGalois K p.SplittingField := IsGalois.of_separable_splitting_field hsep
  have hdeg : (p.map (algebraMap K p.SplittingField)).degree ≠ 0 := by
    rw [Polynomial.degree_map, hp, Polynomial.degree_X_pow_sub_C hn]
    exact_mod_cast hn.ne'
  obtain ⟨α, hαroot⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hdeg
  have hα : α ^ n = algebraMap K p.SplittingField a := by
    have := hαroot
    simp only [hp, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
    exact sub_eq_zero.1 this
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K p.SplittingField).injective (by simpa using hα.symm))
  have hζL : IsPrimitiveRoot (algebraMap K p.SplittingField ζ) n :=
    hζ.map_of_injective (algebraMap K p.SplittingField).injective
  have hgen : IntermediateField.adjoin K {α} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin K (p.rootSet p.SplittingField : Set p.SplittingField) := by
      rw [Polynomial.IsSplittingField.adjoin_rootSet]; trivial
    refine Algebra.adjoin_le (S := (IntermediateField.adjoin K {α}).toSubalgebra) ?_ hx
    intro y hy
    rw [Polynomial.mem_rootSet] at hy
    have hy' : y ^ n = algebraMap K p.SplittingField a := by
      have := hy.2
      simp only [hp, Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C] at this
      exact sub_eq_zero.1 this
    have h1 : (y / α) ^ n = 1 := by
      rw [div_pow, hy', hα, div_self]
      exact (map_ne_zero _).2 ha
    have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨j, -, hj⟩ := hζL.eq_pow_of_pow_eq_one h1
    have : y = algebraMap K p.SplittingField (ζ ^ j) * α := by
      rw [map_pow, hj]; field_simp
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self K α)
  have hcomm : ∀ σ τ : Gal(p.SplittingField/K), σ * τ = τ * σ := by
    intro σ τ
    apply gal_ext_of_gen hgen
    obtain ⟨i, -, hi⟩ := kummer_zeta hn hζ a ha p.SplittingField α hα σ
    obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ a ha p.SplittingField α hα τ
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hj, hi, map_mul, map_mul, AlgEquiv.commutes,
      AlgEquiv.commutes, hi, hj]
    ring
  have : IsAbelianGalois K p.SplittingField := { toIsMulCommutative := ⟨⟨hcomm⟩⟩ }
  obtain ⟨m, hm⟩ := hR.exists_definingModulus p.SplittingField
  have hsub : m.finiteSupport ⊆ Sset n {a} := by
    intro v hv
    rw [hm.finiteSupport_eq] at hv
    by_contra hvS
    exact hv (item_5_3 n hn ζ hζ a ha p.SplittingField α hα hgen v hvS).1
  refine ⟨m, hsub, ?_⟩
  intro b b' hb hb' hbb'
  have hc : b * b'⁻¹ ∈ sIdeals m.finiteSupport := fun v hv =>
    (sIdeals (Sset n {a})).mul_mem hb ((sIdeals (Sset n {a})).inv_mem hb') v (hsub hv)
  have hker : artinMap p.SplittingField m.finiteSupport ⟨b * b'⁻¹, hc⟩ = 1 := by
    have : (⟨b * b'⁻¹, hc⟩ : sIdeals m.finiteSupport) ∈ (artinMap p.SplittingField m.finiteSupport).ker := by
      rw [hm.ker_eq, Subgroup.mem_subgroupOf]
      exact (le_sup_left : rayPrincipal m ≤ _) hbb'
    exact this
  let B : sIdeals (Sset n {a}) := ⟨b, hb⟩
  let B' : sIdeals (Sset n {a}) := ⟨b', hb'⟩
  have h1 : artinMap p.SplittingField (Sset n {a}) B * (artinMap p.SplittingField (Sset n {a}) B')⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact hker
  have h2 := mul_inv_eq_one.1 h1
  have e := item_5_3_ideal n hn ζ hζ a ha p.SplittingField α hα hgen B
  have e' := item_5_3_ideal n hn ζ hζ a ha p.SplittingField α hα hgen B'
  rw [h2, e'] at e
  exact (algebraMap K p.SplittingField).injective (mul_right_cancel₀ hα0 e).symm

/-! ## The Hilbert symbol -/

section Hilbert

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

open Classical in
/-- **The Hilbert symbol $(a,b)_v$ of order $n$ at a finite prime** (Milne, *CFT*, VIII, Remark 5.9 formula, p. 247;
see the module docstring): for $L = K(\alpha)$, $\alpha^n = a$, an idèlic Artin map $\phi$ of $L/K$ and $b \in
K^\times$, the $\mu \in K$ with $\phi(\iota_v b)(\alpha) = \mu\,\alpha$ ($\iota_v b$ the idèle with component $b$ at
$v$ and $1$ elsewhere); $1$ if there is none. -/
@[kb "milne2020cft" "Ch. VIII, §5, p. 246 (Hilbert symbol (a,b)_v), via Remark 5.9, p. 247"]
def hilbertArtin (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) : K :=
  if h : ∃ μ : K, φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L μ * α then h.choose else 1

open Classical in
/-- The Hilbert symbol $(a,b)_w$ at an infinite prime $w$ (as `hilbertArtin`). -/
def hilbertArtinInf (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (w : InfinitePlace K) (b : Kˣ) : K :=
  if h : ∃ μ : K, φ (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L μ * α then h.choose else 1

/-- The Kummer character: for $\alpha^n = a$ with $\zeta_n \in K$, $\sigma \mapsto \sigma(\alpha)/\alpha$ is a
homomorphism $\mathrm{Gal}(L/K) \to L^\times$. -/
theorem exists_kummerChar (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (α : L) (hα : α ^ n = algebraMap K L a) :
    ∃ ε : Gal(L/K) →* Lˣ, ∀ σ : Gal(L/K), σ α = ((ε σ : Lˣ) : L) * α := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  refine ⟨{ toFun := fun σ => Units.mk0 (σ α / α) (div_ne_zero ((map_ne_zero σ).2 hα0) hα0)
            map_one' := by ext; simp [hα0]
            map_mul' := fun σ τ => by
              obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ a ha L α hα τ
              ext
              simp only [Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
              rw [hj, map_mul, AlgEquiv.commutes]
              field_simp }, fun σ => ?_⟩
  change σ α = (σ α / α) * α
  field_simp

theorem kummerChar_eq {α : L} {ε : Gal(L/K) →* Lˣ} (hε : ∀ σ : Gal(L/K), σ α = ((ε σ : Lˣ) : L) * α) (hα0 : α ≠ 0)
    {σ : Gal(L/K)} {μ : K} (h : σ α = algebraMap K L μ * α) : ((ε σ : Lˣ) : L) = algebraMap K L μ :=
  mul_right_cancel₀ hα0 ((hε σ).symm.trans h)

open Classical in
theorem dite_choose_eq {α : L} (hα0 : α ≠ 0) (σ : Gal(L/K)) (μ : K) (h : σ α = algebraMap K L μ * α) :
    (if h' : ∃ μ' : K, σ α = algebraMap K L μ' * α then h'.choose else 1) = μ := by
  have h' : ∃ μ' : K, σ α = algebraMap K L μ' * α := ⟨μ, h⟩
  simp only [h', ↓reduceDIte]
  exact (algebraMap K L).injective (mul_right_cancel₀ hα0 (h'.choose_spec.symm.trans h))

theorem hilbertArtin_eq (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (hα0 : α ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (μ : K)
    (h : φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L μ * α) : hilbertArtin L φ α v b = μ := by
  unfold hilbertArtin
  exact dite_choose_eq L hα0 _ μ h

theorem hilbertArtinInf_eq (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (hα0 : α ≠ 0)
    (w : InfinitePlace K) (b : Kˣ) (μ : K)
    (h : φ (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L μ * α) : hilbertArtinInf L φ α w b = μ := by
  unfold hilbertArtinInf
  exact dite_choose_eq L hα0 _ μ h

/-- The Hilbert symbol satisfies its defining equation (the Kummer extension has all the needed roots of unity). -/
theorem hilbertArtin_spec (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (α : L) (hα : α ^ n = algebraMap K L a) (φ : IdeleGroup (𝓞 K) K →* Gal(L/K))
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :
    φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L (hilbertArtin L φ α v b) * α := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ a ha L α hα
    (φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (algebraMap K _).toMonoidHom b)))
  rw [hilbertArtin_eq L φ α hα0 v b _ hj]
  exact hj

theorem hilbertArtinInf_spec (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (α : L) (hα : α ^ n = algebraMap K L a) (φ : IdeleGroup (𝓞 K) K →* Gal(L/K))
    (w : InfinitePlace K) (b : Kˣ) :
    φ (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)) α =
      algebraMap K L (hilbertArtinInf L φ α w b) * α := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ a ha L α hα
    (φ (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)))
  rw [hilbertArtinInf_eq L φ α hα0 w b _ hj]
  exact hj

/-- An idèle that is a unit at an unramified prime $v$ (and $1$ elsewhere) has trivial image. -/
theorem phi_unit_eq_one (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  obtain ⟨N, hN⟩ := hφ.local_ramified
  apply hN
  · intro v' hv'
    by_cases h : v' = v
    · subst h; rw [ideleFinAt_ofAdic_self]; exact hu
    · rw [ideleFinAt_ofAdic_ne h]; simp
  · intro v' hv'
    have : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [ideleFinAt_ofAdic_ne this]; simp
  · intro w hw _
    rw [ideleInfAt_ofAdic]
    unfold IsPosAt; simp

/-- **5.8** (Milne, *CFT*, VIII, 5.8, p. 246): for $v \notin S(a)$, $(a,b)_v = (a/\mathfrak p_v)^{\mathrm{ord}_v(b)}$. -/
@[kb "milne2020cft" "Ch. VIII, 5.8, p. 246"]
theorem item_5_8 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0) (α : L)
    (hα : α ^ n = algebraMap K L a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ Sset n {a}) (b : Kˣ) :
    hilbertArtin L φ α v b =
      powerResidue n a v ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K)) := by
  classical
  obtain ⟨hunr, hfr⟩ := item_5_3 n hn ζ hζ a ha L α hα hgen v hv
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  obtain ⟨ε, hε⟩ := exists_kummerChar L n hn ζ hζ a ha α hα
  obtain ⟨π, hπ⟩ := exists_unit_uniformizer v
  set b' : (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b with hb'
  set k : ℤ := FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K)) with hk
  have hbv : Valued.v (b' : v.adicCompletion K) = WithZero.exp (-k) := by
    show Valued.v (algebraMap K (v.adicCompletion K) (b : K)) = _
    have hι : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
      fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    rw [hι,
      QuadFormsKB.Analysis.valuation_eq_exp_neg_count v b.ne_zero]
  set u : (v.adicCompletion K)ˣ := (π ^ k)⁻¹ * b' with hu
  have huv : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
      map_zpow₀, hπ, hbv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hdec : IdeleGroup.ofAdicCompletion (𝓞 K) K v b' =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v π ^ k * IdeleGroup.ofAdicCompletion (𝓞 K) K v u := by
    rw [← map_zpow, ← map_mul, hu, mul_inv_cancel_left]
  have hφ1 : φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v b') = artinFrob L v ^ k := by
    rw [hdec, map_mul, map_zpow, hφ.frobenius v hunr π hπ, phi_unit_eq_one L φ hφ v hunr u huv, mul_one]
  have h1 : ((ε (φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v b')) : Lˣ) : L) =
      algebraMap K L (powerResidue n a v ^ k) := by
    rw [hφ1, map_zpow, Units.val_zpow_eq_zpow_val, kummerChar_eq L hε hα0 hfr, map_zpow₀]
  exact hilbertArtin_eq L φ α hα0 v b _ (by rw [hε, h1])

theorem ideleFinAt_prod {ι : Type*} (s : Finset ι) (f : ι → IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (∏ i ∈ s, f i) v = ∏ i ∈ s, ideleFinAt (f i) v := by
  let F : IdeleGroup (𝓞 K) K →* v.adicCompletion K := ⟨⟨fun x => ideleFinAt x v, rfl⟩, fun _ _ => rfl⟩
  exact map_prod F f s

theorem ideleInfAt_prod {ι : Type*} (s : Finset ι) (f : ι → IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    ideleInfAt (∏ i ∈ s, f i) w = ∏ i ∈ s, ideleInfAt (f i) w := by
  let F : IdeleGroup (𝓞 K) K →* w.Completion := ⟨⟨fun x => ideleInfAt x w, rfl⟩, fun _ _ => rfl⟩
  exact map_prod F f s

theorem ideleFinAt_ofCompletion (w : InfinitePlace K) (z : w.Completionˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (IdeleGroup.ofCompletion (𝓞 K) K w z) v = 1 := rfl

theorem ideleInfAt_ofCompletion_self (w : InfinitePlace K) (z : w.Completionˣ) :
    ideleInfAt (IdeleGroup.ofCompletion (𝓞 K) K w z) w = z := by
  classical
  simp [ideleInfAt]

theorem ideleInfAt_ofCompletion_ne {w w' : InfinitePlace K} (h : w' ≠ w) (z : w'.Completionˣ) :
    ideleInfAt (IdeleGroup.ofCompletion (𝓞 K) K w' z) w = 1 := by
  classical
  simp [ideleInfAt, h]

/-- **5.10, the product formula** (Milne, *CFT*, VIII, 5.10, p. 247): for $a, b \in K^\times$,
$\prod_v (a,b)_v = 1$, the product over all primes (finite and infinite), given an idèlic Artin map of
$K[a^{1/n}]/K$ trivial on $K^\times$ (the reciprocity law). -/
@[kb "milne2020cft" "Ch. VIII, 5.10, p. 247"]
theorem item_5_10 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0) (α : L)
    (hα : α ^ n = algebraMap K L a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hφK : ∀ c : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) (b : Kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), hilbertArtin L φ α v b) * ∏ w : InfinitePlace K, hilbertArtinInf L φ α w b
      = 1 := by
  classical
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  obtain ⟨ε, hε⟩ := exists_kummerChar L n hn ζ hζ a ha α hα
  let b' : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v =>
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b
  let bw : ∀ w : InfinitePlace K, w.Completionˣ := fun w =>
    Units.map (algebraMap K w.Completion).toMonoidHom b
  have hfinT : ((unramifiedPrimes K L)ᶜ ∪
      {v : HeightOneSpectrum (𝓞 K) | Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K b) v) ≠ 1}).Finite :=
    (finite_compl_unramifiedPrimes K L).union (finite_valued_ne_one _)
  set T := hfinT.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∉ unramifiedPrimes K L ∨
      Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K b) v) ≠ 1 := fun v => by
    simp [hT]
  let A : IdeleGroup (𝓞 K) K := (∏ v ∈ T, IdeleGroup.ofAdicCompletion (𝓞 K) K v (b' v)) *
    ∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (bw w)
  have hbne : ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (b : K) ≠ 0 := fun v =>
    (map_ne_zero _).2 b.ne_zero
  have hFin : ∀ v, ideleFinAt A v = if v ∈ T then algebraMap K (v.adicCompletion K) (b : K) else 1 := by
    intro v
    show ideleFinAt (∏ v ∈ T, IdeleGroup.ofAdicCompletion (𝓞 K) K v (b' v)) v *
      ideleFinAt (∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (bw w)) v = _
    rw [ideleFinAt_prod, ideleFinAt_prod]
    simp only [ideleFinAt_ofCompletion, Finset.prod_const_one, mul_one]
    by_cases hv : v ∈ T
    · rw [Finset.prod_eq_single_of_mem v hv, if_pos hv, ideleFinAt_ofAdic_self]
      · rfl
      · intro v' _ hne
        exact ideleFinAt_ofAdic_ne (Ne.symm hne) _
    · rw [if_neg hv]
      exact Finset.prod_eq_one fun v' hv' => ideleFinAt_ofAdic_ne (fun h => hv (by rw [h]; exact hv')) _
  have hInf : ∀ w, ideleInfAt A w = algebraMap K w.Completion (b : K) := by
    intro w
    show ideleInfAt (∏ v ∈ T, IdeleGroup.ofAdicCompletion (𝓞 K) K v (b' v)) w *
      ideleInfAt (∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (bw w)) w = _
    rw [ideleInfAt_prod, ideleInfAt_prod]
    simp only [ideleInfAt_ofAdic, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single_of_mem w (Finset.mem_univ w), ideleInfAt_ofCompletion_self]
    · rfl
    · intro w' _ hne
      exact ideleInfAt_ofCompletion_ne hne _
  have hφU : φ (IdeleGroup.unitEmbedding (𝓞 K) K b * A⁻¹) = 1 := by
    obtain ⟨N, hN⟩ := hφ.local_ramified
    apply hN
    · intro v hv
      rw [ideleFinAt_mul, ideleFinAt_inv, hFin, ideleFinAt_unitEmbedding]
      by_cases hvT : v ∈ T
      · rw [if_pos hvT, mul_inv_cancel₀ (hbne v), map_one]
      · rw [if_neg hvT, inv_one, mul_one, ← ideleFinAt_unitEmbedding]
        by_contra hne
        exact hvT ((hmemT v).2 (Or.inr hne))
    · intro v hv
      have hvT : v ∈ T := (hmemT v).2 (Or.inl hv)
      rw [ideleFinAt_mul, ideleFinAt_inv, hFin, ideleFinAt_unitEmbedding, if_pos hvT, mul_inv_cancel₀ (hbne v),
        sub_self, map_zero]
      exact zero_le
    · intro w hw _
      rw [ideleInfAt_mul, ideleInfAt_inv, hInf]
      have : ideleInfAt (IdeleGroup.unitEmbedding (𝓞 K) K b) w = algebraMap K w.Completion (b : K) := rfl
      rw [this, mul_inv_cancel₀ ((map_ne_zero _).2 b.ne_zero)]
      unfold IsPosAt; simp
  have hφA : φ A = 1 := by
    rw [map_mul, hφK, one_mul, map_inv, inv_eq_one] at hφU
    exact hφU
  have hprod : algebraMap K L ((∏ v ∈ T, hilbertArtin L φ α v b) * ∏ w : InfinitePlace K, hilbertArtinInf L φ α w b)
      = 1 := by
    have h1 : ((ε (φ A) : Lˣ) : L) = 1 := by rw [hφA, map_one]; rfl
    rw [show φ A = (∏ v ∈ T, φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v (b' v))) *
      ∏ w : InfinitePlace K, φ (IdeleGroup.ofCompletion (𝓞 K) K w (bw w)) by
        simp only [A, map_mul, map_prod]] at h1
    rw [map_mul, map_prod, map_prod, Units.val_mul, Units.coe_prod, Units.coe_prod] at h1
    rw [map_mul, map_prod, map_prod, ← h1]
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      exact (kummerChar_eq L hε hα0 (hilbertArtin_spec L n hn ζ hζ a ha α hα φ v b)).symm
    · refine Finset.prod_congr rfl fun w _ => ?_
      exact (kummerChar_eq L hε hα0 (hilbertArtinInf_spec L n hn ζ hζ a ha α hα φ w b)).symm
  have hone : ∀ v ∉ T, hilbertArtin L φ α v b = 1 := by
    intro v hvT
    have hv1 : v ∈ unramifiedPrimes K L := by
      by_contra h; exact hvT ((hmemT v).2 (Or.inl h))
    have hv2 : Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K b) v) = 1 := by
      by_contra h; exact hvT ((hmemT v).2 (Or.inr h))
    refine hilbertArtin_eq L φ α hα0 v b 1 ?_
    rw [phi_unit_eq_one L φ hφ v hv1 (b' v) hv2]
    simp
  have hfp : ∏ᶠ v : HeightOneSpectrum (𝓞 K), hilbertArtin L φ α v b = ∏ v ∈ T, hilbertArtin L φ α v b := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    exact hv (hone v hvT)
  rw [hfp]
  exact (algebraMap K L).injective (by rw [hprod, map_one])

end Hilbert

variable (K) in
/-- **5.7** (Milne, *CFT*, VIII, 5.7, p. 246, proved there through
$A(b,a;\zeta) \cong A(a,b;\zeta^{-1}) \cong A(a,b;\zeta)^{\mathrm{opp}}$): for $n \ge 1$, if $K$ contains a primitive
$n$-th root of unity $\zeta$ (Milne's standing hypotheses in §5, not an erratum), then $(b,a)_v = (a,b)_v^{-1}$ at every finite and
infinite prime. Stated for the symbols `hilbertArtin` of the two Kummer extensions $K[a^{1/n}]$, $K[b^{1/n}]$
with their idèlic Artin maps. Proved unconditionally in `Item57Uncond.lean` (`item5_7`). The form without
$\zeta \in K$ is `Item5_7NoRoot`, false (`not_item5_7_rat`). -/
@[kb "milne2020cft" "Ch. VIII, 5.7, p. 246"]
structure Item5_7 (n : ℕ) : Prop where
  skew : 0 < n → ∀ ζ : K, IsPrimitiveRoot ζ n →
    ∀ (La : Type) [Field La] [NumberField La] [Algebra K La] [IsAbelianGalois K La]
    (Lb : Type) [Field Lb] [NumberField Lb] [Algebra K Lb] [IsAbelianGalois K Lb]
    (a b : Kˣ) (α : La) (β : Lb), α ^ n = algebraMap K La a → β ^ n = algebraMap K Lb b →
    IntermediateField.adjoin K {α} = ⊤ → IntermediateField.adjoin K {β} = ⊤ →
    ∀ (φa : IdeleGroup (𝓞 K) K →* Gal(La/K)) (φb : IdeleGroup (𝓞 K) K →* Gal(Lb/K)),
      IsIdelicArtinMap La φa → IsIdelicArtinMap Lb φb →
      (∀ c : Kˣ, φa (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) →
      (∀ c : Kˣ, φb (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) →
      (∀ v, hilbertArtin Lb φb β v a * hilbertArtin La φa α v b = 1) ∧
        (∀ w, hilbertArtinInf Lb φb β w a * hilbertArtinInf La φa α w b = 1)

variable (K) in
/-- The earlier formalization of 5.7 **without** Milne's hypothesis that $K$ contains a primitive $n$-th root of
unity. It is false (`not_item5_7_rat`, $K = \mathbb Q$, $n = 4$); the hypothesis is Milne's (§5 assumes
$\zeta_n \in K$ throughout), so this is a formalization defect, not an erratum. Kept so that the counterexample still
type-checks; the statement of 5.7 is `Item5_7`. -/
@[kb "milne2020cft" "Ch. VIII, 5.7, p. 246 (form without ζ_n ∈ K; false)"]
structure Item5_7NoRoot (n : ℕ) : Prop where
  skew : ∀ (La : Type) [Field La] [NumberField La] [Algebra K La] [IsAbelianGalois K La]
    (Lb : Type) [Field Lb] [NumberField Lb] [Algebra K Lb] [IsAbelianGalois K Lb]
    (a b : Kˣ) (α : La) (β : Lb), α ^ n = algebraMap K La a → β ^ n = algebraMap K Lb b →
    IntermediateField.adjoin K {α} = ⊤ → IntermediateField.adjoin K {β} = ⊤ →
    ∀ (φa : IdeleGroup (𝓞 K) K →* Gal(La/K)) (φb : IdeleGroup (𝓞 K) K →* Gal(Lb/K)),
      IsIdelicArtinMap La φa → IsIdelicArtinMap Lb φb →
      (∀ c : Kˣ, φa (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) →
      (∀ c : Kˣ, φb (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) →
      (∀ v, hilbertArtin Lb φb β v a * hilbertArtin La φa α v b = 1) ∧
        (∀ w, hilbertArtinInf Lb φb β w a * hilbertArtinInf La φa α w b = 1)

theorem finite_val_ne_one (x : K) (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | v.valuation K x ≠ 1}.Finite := by
  have := finite_valued_ne_one (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 x hx))
  refine this.subset fun v hv => ?_
  have hι : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  simp only [Set.mem_setOf_eq, ideleFinAt_unitEmbedding, Units.val_mk0]
  rwa [hι]

/-- The set $S(a)$ is finite for $a \neq 0$ and $n > 0$. -/
theorem finite_Sset (n : ℕ) (hn : 0 < n) (a : K) (ha : a ≠ 0) :
    (Sset n {a} : Set (HeightOneSpectrum (𝓞 K))).Finite := by
  have h1 := finite_val_ne_one (n : K) (Nat.cast_ne_zero.2 hn.ne')
  have h2 := finite_val_ne_one a ha
  refine (h1.union h2).subset fun v hv => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  have hnv : (n : 𝓞 K) ∉ v.asIdeal := fun hm => by
    have := (v.valuation_lt_one_iff_mem (K := K) (n : 𝓞 K)).2 hm
    simp at this
    exact this.ne hcon.1
  exact ((notMem_Sset_iff v n a).2 ⟨hnv, hcon.2⟩) hv

theorem count_eq_zero_of_val (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) (h : v.valuation K x = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 := by
  rw [QuadFormsKB.Analysis.valuation_eq_exp_neg_count v hx, ← WithZero.exp_zero, WithZero.exp_inj] at h
  omega

/-- **Theorem 5.11, the power reciprocity law** (Milne, *CFT*, VIII, Theorem 5.11, p. 247; from 5.7
(`Item5_7`, proved in `Item57Uncond.lean`, where `theorem_5_11_uncond` drops this hypothesis) and idèlic Artin maps
trivial on $K^\times$): let $a, b \in K^\times$ with $S(a) \cap S(b) = S$. Then
$$\Big(\frac ab\Big)\Big(\frac ba\Big)^{-1} = \prod_{v \in S}(b,a)_v,$$
*Erratum:* the product must include the infinite primes (for $n = 2$ the real primes contribute: $K = \mathbb Q$,
$a = b = -1$ gives $1$ on the left and $(-1,-1)_2 = -1$ over $S = \{2\}$). Here the right side is the product over
$v \in S$ and over all infinite primes. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.11, p. 247 (power reciprocity law)"]
theorem theorem_5_11 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (h57 : Item5_7 K n)
    (La : Type) [Field La] [NumberField La] [Algebra K La] [IsAbelianGalois K La]
    (Lb : Type) [Field Lb] [NumberField Lb] [Algebra K Lb] [IsAbelianGalois K Lb]
    (a b : Kˣ) (α : La) (β : Lb) (hα : α ^ n = algebraMap K La a) (hβ : β ^ n = algebraMap K Lb b)
    (hαg : IntermediateField.adjoin K {α} = ⊤) (hβg : IntermediateField.adjoin K {β} = ⊤)
    (φa : IdeleGroup (𝓞 K) K →* Gal(La/K)) (φb : IdeleGroup (𝓞 K) K →* Gal(Lb/K))
    (hφa : IsIdelicArtinMap La φa) (hφb : IsIdelicArtinMap Lb φb)
    (hφaK : ∀ c : Kˣ, φa (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (hφbK : ∀ c : Kˣ, φb (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (hS : Sset n {(a : K)} ∩ Sset n {(b : K)} = Sset n ∅) :
    powerResidueElt n (a : K) b * (powerResidueElt n (b : K) a)⁻¹ =
      (∏ᶠ v ∈ Sset n (∅ : Set K), hilbertArtin Lb φb β v a) * ∏ w : InfinitePlace K, hilbertArtinInf Lb φb β w a := by
  classical
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hb : (b : K) ≠ 0 := b.ne_zero
  have hSa : (Sset n {(a : K)}).Finite := finite_Sset n hn _ ha
  have hSb : (Sset n {(b : K)}).Finite := finite_Sset n hn _ hb
  set T := (hSa.union hSb).toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∈ Sset n {(a : K)} ∨ v ∈ Sset n {(b : K)} := fun v => by simp [hT]
  have hSsa : ∀ v, v ∈ Sset n (∅ : Set K) → v ∈ Sset n {(a : K)} := fun v hv => by
    rcases hv with hv | ⟨x, hx, -⟩
    · exact Or.inl hv
    · exact absurd hx (Set.notMem_empty x)
  have hSsb : ∀ v, v ∈ Sset n (∅ : Set K) → v ∈ Sset n {(b : K)} := fun v hv => by
    rcases hv with hv | ⟨x, hx, -⟩
    · exact Or.inl hv
    · exact absurd hx (Set.notMem_empty x)
  have hSab : ∀ v, v ∈ Sset n {(a : K)} → v ∈ Sset n {(b : K)} → v ∈ Sset n (∅ : Set K) := fun v h1 h2 => by
    have : v ∈ Sset n {(a : K)} ∩ Sset n {(b : K)} := ⟨h1, h2⟩
    rwa [hS] at this
  obtain ⟨hskew, hskewI⟩ := h57.skew hn ζ hζ La Lb a b α β hα hβ hαg hβg φa φb hφa hφb hφaK hφbK
  have hfg : ∀ v, hilbertArtin Lb φb β v a = (hilbertArtin La φa α v b)⁻¹ := fun v =>
    eq_inv_of_mul_eq_one_left (hskew v)
  have hf1 : ∀ v ∉ T, hilbertArtin La φa α v b = 1 := by
    intro v hvT
    rw [hmemT, not_or] at hvT
    rw [item_5_8 La n hn ζ hζ a ha α hα hαg φa hφa v hvT.1 b]
    have : v.valuation K (b : K) = 1 := ((notMem_Sset_iff v n _).1 hvT.2).2
    rw [count_eq_zero_of_val v _ hb this, zpow_zero]
  have hg1 : ∀ v ∉ T, hilbertArtin Lb φb β v a = 1 := fun v hv => by rw [hfg, hf1 v hv, inv_one]
  have E1 : powerResidueElt n (a : K) b = ∏ v ∈ T, (if v ∈ Sset n {(a : K)} then 1 else hilbertArtin La φa α v b) := by
    unfold powerResidueElt
    refine Eq.trans (finprod_congr fun v => ?_) (finprod_eq_prod_of_mulSupport_subset _ ?_)
    · by_cases hv : v ∈ Sset n {(a : K)}
      · simp [hv]
      · simp only [hv, if_false]
        exact (item_5_8 La n hn ζ hζ a ha α hα hαg φa hφa v hv b).symm
    · intro v hv
      by_contra hvT
      exact (Function.mem_mulSupport.1 hv) (by simp [hf1 v hvT])
  have E2 : powerResidueElt n (b : K) a = ∏ v ∈ T, (if v ∈ Sset n {(b : K)} then 1 else hilbertArtin Lb φb β v a) := by
    unfold powerResidueElt
    refine Eq.trans (finprod_congr fun v => ?_) (finprod_eq_prod_of_mulSupport_subset _ ?_)
    · by_cases hv : v ∈ Sset n {(b : K)}
      · simp [hv]
      · simp only [hv, if_false]
        exact (item_5_8 Lb n hn ζ hζ b hb β hβ hβg φb hφb v hv a).symm
    · intro v hv
      by_contra hvT
      exact (Function.mem_mulSupport.1 hv) (by simp [hg1 v hvT])
  have hfp : ∏ᶠ v : HeightOneSpectrum (𝓞 K), hilbertArtin La φa α v b = ∏ v ∈ T, hilbertArtin La φa α v b :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      by_contra hvT
      exact (Function.mem_mulSupport.1 hv) (hf1 v hvT)
  have hP := item_5_10 La n hn ζ hζ a ha α hα hαg φa hφa hφaK b
  rw [hfp] at hP
  set t := T.filter (fun v => v ∈ Sset n (∅ : Set K)) with ht
  have hR : ∏ᶠ v ∈ Sset n (∅ : Set K), hilbertArtin Lb φb β v a = ∏ v ∈ t, hilbertArtin Lb φb β v a := by
    refine finprod_mem_eq_prod_of_subset _ ?_ ?_
    · rintro v ⟨hvS, hvg⟩
      rw [Finset.mem_coe, ht, Finset.mem_filter]
      refine ⟨?_, hvS⟩
      by_contra hvT
      exact hvg (hg1 v hvT)
    · intro v hv
      exact (Finset.mem_filter.1 hv).2
  have hinf : ∏ w : InfinitePlace K, hilbertArtinInf Lb φb β w a =
      (∏ w : InfinitePlace K, hilbertArtinInf La φa α w b)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun w _ => eq_inv_of_mul_eq_one_left (hskewI w)
  have hP1 : ∏ v ∈ t, hilbertArtin Lb φb β v a = (∏ v ∈ t, hilbertArtin La φa α v b)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => hfg v
  have e2 : (∏ v ∈ T, (if v ∈ Sset n {(b : K)} then 1 else hilbertArtin Lb φb β v a))⁻¹ =
      ∏ v ∈ T, (if v ∈ Sset n {(b : K)} then 1 else hilbertArtin La φa α v b) := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases h : v ∈ Sset n {(b : K)}
    · simp [h]
    · simp [h, hfg]
  have e3 : (∏ v ∈ T, (if v ∈ Sset n {(a : K)} then 1 else hilbertArtin La φa α v b)) *
      ∏ v ∈ T, (if v ∈ Sset n {(b : K)} then 1 else hilbertArtin La φa α v b) =
      ∏ v ∈ T, (if v ∈ Sset n (∅ : Set K) then 1 else hilbertArtin La φa α v b) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    by_cases h1 : v ∈ Sset n {(a : K)}
    · by_cases h2 : v ∈ Sset n {(b : K)}
      · simp [h1, h2, hSab v h1 h2]
      · have : v ∉ Sset n (∅ : Set K) := fun h => h2 (hSsb v h)
        simp [h1, h2, this]
    · have h2 : v ∈ Sset n {(b : K)} := ((hmemT v).1 hv).resolve_left h1
      have : v ∉ Sset n (∅ : Set K) := fun h => h1 (hSsa v h)
      simp [h1, h2, this]
  have e4 : ∏ v ∈ T, (if v ∈ Sset n (∅ : Set K) then 1 else hilbertArtin La φa α v b) =
      ∏ v ∈ T.filter (fun v => ¬ v ∈ Sset n (∅ : Set K)), hilbertArtin La φa α v b := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases h : v ∈ Sset n (∅ : Set K) <;> simp [h]
  have e5 := Finset.prod_filter_mul_prod_filter_not T (fun v => v ∈ Sset n (∅ : Set K))
    (fun v => hilbertArtin La φa α v b)
  rw [← ht] at e5
  rw [E1, E2, hR, hinf, hP1, e2, e3, e4, ← mul_inv]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hP, ← e5]
  ring

end NumberFieldKB.MilneCFT.Ch8
