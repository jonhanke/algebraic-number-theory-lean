import NumberFieldKB.MilneCFT.Ch8.SteinbergNorm
import NumberFieldKB.MilneCFT.LocalCFT.Basic
import NumberFieldKB.MilneCFT.Ch3Kummer
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The Hilbert pairing of order $p$ from a local Artin map (for Milne, *CFT*, VIII, Prop. 5.12)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`: Chapter III, Remark 4.5
(p. 114): the Hilbert symbol and the local Artin map are related by $\phi_K(b)(\alpha) = (a, b)\,\alpha$ for
$\alpha^n = a$; Chapter VIII, Prop. 5.12 (p. 248) uses the order-$p$ symbol of $\mathbb Q_p[\zeta_p]$.

**Setting.** $K$ is a nonarchimedean local field (`IsNonarchimedeanLocalField`), $\Omega$ a separable closure, $p$ a
prime and $\zeta \in K$ a primitive $p$-th root of unity, and `φ` a local Artin map (`IsLocalArtinMap`, Milne I,
Theorem 1.1; its existence is the named input `LocalCFT.LocalReciprocityExistence`, proved in Tau Ceti as
`localArtinEquiv`, not importable here).

## What is formalized
* `hilbertPairing φ hζ : Kˣ →* Kˣ →* Kˣ`: $(a, b)$ is the root of unity $\phi(b)(\alpha)/\alpha$, for $\alpha \in \Omega$
  with $\alpha^p = a$, computed in the cyclic extension $K(\alpha)$ (independent of $\alpha$ and of the finite abelian
  extension used, by the compatibility of $\phi$; `hilbertPairing_spec`). This is Milne's symbol through Remark III.4.5.
* `hilbertPairing_isSteinberg`: it is a Steinberg pairing of exponent $p$ (values in $\mu_p$; $(a, 1 - a) = 1$ because
  $1 - a$ is a norm from $K(\alpha)$, `isSteinbergPairing_of_norm`, and $\ker \phi_{K(\alpha)}$ is the norm group).
* `hilbertPairing_isExplicitPairing`: hence, for $\lambda \in K^\times$ and $\eta_i = 1 - \lambda^i$ with
  $\eta_k \in K^{\times p}$ for $k \ge p + 1$, it satisfies (a)–(c) of Prop. 5.12 on the generators, with
  $z = (\eta_p, \lambda)$.
-/

open scoped ValuativeRel
open IntermediateField NumberFieldKB.MilneCFT.LocalCFT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable {p : ℕ} [Fact p.Prime] {ζ : Kˣ}

/-- Every $a \in K^\times$ has a $p$-th root in $\Omega$ ($p \ne 0$ in $K$ since $\zeta$ is a primitive $p$-th root). -/
theorem exists_pthRoot (hζ : IsPrimitiveRoot ζ p) (a : Kˣ) : ∃ α : Ω, α ^ p = algebraMap K Ω a := by
  have : NeZero (p : K) := (IsPrimitiveRoot.coe_units_iff.mpr hζ).neZero'
  have : NeZero (p : Ω) := ⟨by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr (NeZero.ne _)⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact IsSepClosed.exists_pow_nat_eq _ p

/-- A chosen $p$-th root of $a$ in $\Omega$. -/
def pthRoot (hζ : IsPrimitiveRoot ζ p) (a : Kˣ) : Ω := (exists_pthRoot (Ω := Ω) hζ a).choose

theorem pthRoot_pow (hζ : IsPrimitiveRoot ζ p) (a : Kˣ) : pthRoot (Ω := Ω) hζ a ^ p = algebraMap K Ω a :=
  (exists_pthRoot (Ω := Ω) hζ a).choose_spec

theorem kummerAux_ne_zero {α : Ω} {a : Kˣ} (hα : α ^ p = algebraMap K Ω a) : α ≠ 0 := by
  intro h
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hα
  exact a.ne_zero ((map_eq_zero _).mp hα.symm)

theorem exists_unit_mul (hζ : IsPrimitiveRoot ζ p) {α β : Ω} {a : Kˣ} (hα : α ^ p = algebraMap K Ω a)
    (hβ : β ^ p = algebraMap K Ω a) : ∃ u : Kˣ, u ^ p = 1 ∧ β = algebraMap K Ω u * α := by
  have hζ' : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζΩ : IsPrimitiveRoot (algebraMap K Ω ζ) p := hζ'.map_of_injective (algebraMap K Ω).injective
  have hα0 := kummerAux_ne_zero hα
  have h1 : (β / α) ^ p = 1 := by rw [div_pow, hβ, hα, div_self]; simp
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one h1
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · have : algebraMap K Ω ((ζ ^ i : Kˣ) : K) = (algebraMap K Ω ζ) ^ i := by simp
    rw [this, hi, div_mul_cancel₀ _ hα0]

/-- $K(\alpha)$ for $\alpha^p = a$, as a finite abelian extension (Kummer theory, `kummer_adjoin`). -/
def kummerExt (hζ : IsPrimitiveRoot ζ p) {α : Ω} {a : Kˣ} (hα : α ^ p = algebraMap K Ω a) : FiniteAbelianExt K Ω :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := Ch3.kummer_adjoin hζ (α := α) (kummerAux_ne_zero hα) ⟨a, hα.symm⟩
  have : FiniteDimensional K K⟮α⟯ := h.1
  have : IsGalois K K⟮α⟯ := h.2.1
  have : IsCyclic Gal(K⟮α⟯/K) := h.2.2.1
  have : IsAbelianGalois K K⟮α⟯ := IsAbelianGalois.of_isCyclic K K⟮α⟯
  ⟨K⟮α⟯⟩

theorem kummerExt_toField (hζ : IsPrimitiveRoot ζ p) {α : Ω} {a : Kˣ} (hα : α ^ p = algebraMap K Ω a) :
    (kummerExt hζ hα).toField = K⟮α⟯ := rfl

/-- For $\sigma \in \operatorname{Gal}(L/K)$, $L$ finite abelian, and $\alpha \in L$ with $\alpha^p = a$:
$\sigma(\alpha)/\alpha$ is a $p$-th root of unity of $K$. -/
theorem exists_kummerValue (hζ : IsPrimitiveRoot ζ p) (L : FiniteAbelianExt K Ω) (σ : Gal(L.toField/K)) {α : Ω} (hαL : α ∈ L.toField)
    {a : Kˣ} (hα : α ^ p = algebraMap K Ω a) :
    ∃! u : Kˣ, u ^ p = 1 ∧ ((σ ⟨α, hαL⟩ : L.toField) : Ω) = algebraMap K Ω u * α := by
  have hα0 := kummerAux_ne_zero hα
  have hx : (⟨α, hαL⟩ : L.toField) ^ p = algebraMap K L.toField a := Subtype.ext (by simpa using hα)
  have hβp : ((σ ⟨α, hαL⟩ : L.toField) : Ω) ^ p = algebraMap K Ω a := by
    have := congrArg (fun y : L.toField => (σ y : Ω)) hx
    simp only [map_pow, AlgEquiv.commutes] at this
    simpa using this
  obtain ⟨u, hu, hu2⟩ := exists_unit_mul hζ hα hβp
  refine ⟨u, ⟨hu, hu2⟩, ?_⟩
  rintro u' ⟨-, hu'⟩
  apply Units.ext
  apply (algebraMap K Ω).injective
  exact mul_right_cancel₀ hα0 (hu'.symm.trans hu2)

/-- The Kummer value $\sigma(\alpha)/\alpha \in \mu_p(K)$. -/
def kummerValue (hζ : IsPrimitiveRoot ζ p) (L : FiniteAbelianExt K Ω) (σ : Gal(L.toField/K)) {α : Ω} (hαL : α ∈ L.toField)
    {a : Kˣ} (hα : α ^ p = algebraMap K Ω a) : Kˣ :=
  (exists_kummerValue hζ L σ hαL hα).exists.choose

variable {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}

/-- The raw Hilbert symbol $(a, b) = \phi_{K(\alpha)}(b)(\alpha)/\alpha$, $\alpha$ = `pthRoot a`. -/
def hilbertSymbolArtin (hζ : IsPrimitiveRoot ζ p) (φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)) (a b : Kˣ) : Kˣ :=
  kummerValue hζ (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)) (φ _ b)
    (by rw [kummerExt_toField]; exact mem_adjoin_simple_self K _) (pthRoot_pow hζ a)

theorem hilbertSymbolArtin_base (hζ : IsPrimitiveRoot ζ p) (a b : Kˣ) :
    (((φ (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)) b)
      ⟨pthRoot hζ a, by rw [kummerExt_toField]; exact mem_adjoin_simple_self K _⟩ :
        (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)).toField) : Ω) =
      algebraMap K Ω (hilbertSymbolArtin hζ φ a b) * pthRoot hζ a :=
  (exists_kummerValue hζ _ (φ _ b) _ (pthRoot_pow (Ω := Ω) hζ a)).exists.choose_spec.2

theorem coe_unit_mul_apply (L : IntermediateField K Ω) (u : Kˣ) (y : L) :
    (((algebraMap K L (u : K)) * y : L) : Ω) = algebraMap K Ω (u : K) * (y : Ω) := rfl

/-- **Independence**: for every finite abelian $L$ and every $\alpha \in L$ with $\alpha^p = a$,
$\phi_L(b)(\alpha) = (a, b)\,\alpha$ (Milne, III, Remark 4.5). -/
theorem hilbertSymbolArtin_spec (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) (a b : Kˣ) (L : FiniteAbelianExt K Ω) {α : Ω}
    (hαL : α ∈ L.toField) (hα : α ^ p = algebraMap K Ω a) :
    ((φ L b ⟨α, hαL⟩ : L.toField) : Ω) = algebraMap K Ω (hilbertSymbolArtin hζ φ a b) * α := by
  have hα0 := pthRoot_pow (Ω := Ω) hζ a
  obtain ⟨u, -, hu⟩ := exists_unit_mul hζ hα0 hα
  obtain ⟨u', -, hu'⟩ := exists_unit_mul hζ hα hα0
  have hα₀L : pthRoot (Ω := Ω) hζ a ∈ L.toField := by
    rw [hu']; exact mul_mem (L.toField.algebraMap_mem _) hαL
  have hle : (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)).toField ≤ L.toField := by
    rw [kummerExt_toField, IntermediateField.adjoin_simple_le_iff]; exact hα₀L
  have h1 := congrArg (fun σ : Gal((kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)).toField/K) =>
    ((σ ⟨pthRoot hζ a, by rw [kummerExt_toField]; exact mem_adjoin_simple_self K _⟩ :
      (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)).toField) : Ω)) (hφ.compat _ L hle b)
  beta_reduce at h1
  rw [LocalCFT.galRestrict_apply] at h1
  have h3 : ((φ L b ⟨pthRoot hζ a, hα₀L⟩ : L.toField) : Ω) =
      algebraMap K Ω (hilbertSymbolArtin hζ φ a b) * pthRoot hζ a :=
    h1.trans (hilbertSymbolArtin_base (φ := φ) hζ a b)
  have h2 : φ L b ⟨α, hαL⟩ = algebraMap K L.toField u * φ L b ⟨pthRoot hζ a, hα₀L⟩ := by
    have : (⟨α, hαL⟩ : L.toField) = algebraMap K L.toField u * ⟨pthRoot hζ a, hα₀L⟩ :=
      Subtype.ext hu
    rw [this, map_mul, AlgEquiv.commutes]
  rw [h2, coe_unit_mul_apply, h3, hu]
  ring

theorem hilbertSymbolArtin_mul_left (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) (a a' b : Kˣ) :
    hilbertSymbolArtin hζ φ (a * a') b = hilbertSymbolArtin hζ φ a b * hilbertSymbolArtin hζ φ a' b := by
  have hA := pthRoot_pow (Ω := Ω) hζ a
  have hA' := pthRoot_pow (Ω := Ω) hζ a'
  have hmem : ∀ (c : Kˣ), pthRoot (Ω := Ω) hζ c ∈ (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ c)).toField := fun c => by
    rw [kummerExt_toField]; exact mem_adjoin_simple_self K _
  let L : FiniteAbelianExt K Ω :=
    ⟨(kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)).toField ⊔ (kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a')).toField⟩
  have m1 : pthRoot (Ω := Ω) hζ a ∈ L.toField := IsConcreteLE.le_iff.1 le_sup_left (hmem a)
  have m2 : pthRoot (Ω := Ω) hζ a' ∈ L.toField := IsConcreteLE.le_iff.1 le_sup_right (hmem a')
  have hγ : (pthRoot (Ω := Ω) hζ a * pthRoot hζ a') ^ p = algebraMap K Ω ((a * a' : Kˣ) : K) := by
    rw [mul_pow, hA, hA']; simp
  have m3 : pthRoot (Ω := Ω) hζ a * pthRoot hζ a' ∈ L.toField := mul_mem m1 m2
  have e1 := hilbertSymbolArtin_spec hζ hφ a b L m1 hA
  have e2 := hilbertSymbolArtin_spec hζ hφ a' b L m2 hA'
  have e3 := hilbertSymbolArtin_spec hζ hφ (a * a') b L m3 hγ
  have : (⟨pthRoot (Ω := Ω) hζ a * pthRoot hζ a', m3⟩ : L.toField) = ⟨_, m1⟩ * ⟨_, m2⟩ := rfl
  rw [this, map_mul, IntermediateField.coe_mul, e1, e2] at e3
  have hne := mul_ne_zero (kummerAux_ne_zero hA) (kummerAux_ne_zero hA')
  apply Units.ext
  apply (algebraMap K Ω).injective
  apply mul_right_cancel₀ hne
  simp only [Units.val_mul, map_mul]
  linear_combination -e3

theorem hilbertSymbolArtin_mul_right (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) (a b b' : Kˣ) :
    hilbertSymbolArtin hζ φ a (b * b') = hilbertSymbolArtin hζ φ a b * hilbertSymbolArtin hζ φ a b' := by
  have hA := pthRoot_pow (Ω := Ω) hζ a
  set E := kummerExt hζ (pthRoot_pow (Ω := Ω) hζ a)
  have hm : pthRoot (Ω := Ω) hζ a ∈ E.toField := by
    rw [kummerExt_toField]; exact mem_adjoin_simple_self K _
  have e1 := hilbertSymbolArtin_spec hζ hφ a b E hm hA
  have e2 := hilbertSymbolArtin_spec hζ hφ a b' E hm hA
  have e3 := hilbertSymbolArtin_spec hζ hφ a (b * b') E hm hA
  have h2 : φ E b' ⟨pthRoot hζ a, hm⟩ = algebraMap K E.toField (hilbertSymbolArtin hζ φ a b' : K) * ⟨pthRoot hζ a, hm⟩ :=
    Subtype.ext e2
  rw [map_mul, AlgEquiv.mul_apply, h2, map_mul, AlgEquiv.commutes, coe_unit_mul_apply, e1] at e3
  have hne := kummerAux_ne_zero hA
  apply Units.ext
  apply (algebraMap K Ω).injective
  apply mul_right_cancel₀ hne
  simp only [Units.val_mul, map_mul]
  linear_combination -e3

theorem hilbertSymbolArtin_pow (hζ : IsPrimitiveRoot ζ p) (a b : Kˣ) : hilbertSymbolArtin hζ φ a b ^ p = 1 :=
  (exists_kummerValue hζ _ (φ _ b) _ (pthRoot_pow (Ω := Ω) hζ a)).exists.choose_spec.1

/-- **The Hilbert pairing of order $p$** $K^\times \times K^\times \to \mu_p$ defined from a local Artin map
(Milne, III, Remark 4.5). -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.5, p. 114 (Hilbert symbol from the Artin map)"]
def hilbertPairing (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) : Kˣ →* Kˣ →* Kˣ where
  toFun a :=
    { toFun := hilbertSymbolArtin hζ φ a
      map_one' := by
        have h := hilbertSymbolArtin_mul_right hζ hφ a 1 1
        rw [mul_one] at h
        exact (mul_eq_left.mp h.symm)
      map_mul' := hilbertSymbolArtin_mul_right hζ hφ a }
  map_one' := by
    ext1 b
    have h := hilbertSymbolArtin_mul_left hζ hφ 1 1 b
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  map_mul' a a' := by
    ext1 b
    exact hilbertSymbolArtin_mul_left hζ hφ a a' b

/-- **The Hilbert pairing is a Steinberg pairing** of exponent $p$: values in $\mu_p$, and $(a, b) = 1$ when
$a + b = 1$ ($b = 1 - a$ is a norm from $K(\alpha)$, and the kernel of $\phi_{K(\alpha)}$ is the norm group). -/
theorem hilbertPairing_isSteinberg (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) : IsSteinbergPairing (hilbertPairing hζ hφ) p := by
  refine isSteinbergPairing_of_norm (Ω := Ω) (Fact.out) _ (fun x y => hilbertSymbolArtin_pow hζ x y) ?_ ?_
  · intro a
    by_cases h : a = 0
    · exact ⟨0, by rw [h, zero_pow (Fact.out : p.Prime).ne_zero, map_zero]⟩
    · exact exists_pthRoot hζ (Units.mk0 a h)
  · intro a b α hα ⟨x, hx⟩
    set E := kummerExt hζ hα
    have hm : α ∈ E.toField := by
      rw [kummerExt_toField]; exact mem_adjoin_simple_self K _
    have hx0 : x ≠ 0 := fun h => b.ne_zero (hx.symm.trans (Algebra.norm_eq_zero_iff.mpr h))
    have hb : b ∈ (φ E).ker := by
      rw [hφ.ker_eq]
      refine ⟨Units.mk0 x hx0, Units.ext hx⟩
    have e := hilbertSymbolArtin_spec hζ hφ a b E hm hα
    rw [MonoidHom.mem_ker.mp hb] at e
    have hα0 := kummerAux_ne_zero hα
    have : algebraMap K Ω (hilbertSymbolArtin hζ φ a b) = 1 := by
      apply mul_right_cancel₀ hα0
      rw [← e]; simp
    show hilbertSymbolArtin hζ φ a b = 1
    apply Units.ext
    apply (algebraMap K Ω).injective
    simpa using this

/-- **Prop. 5.12, existence on the generators** (Milne, *CFT*, VIII, Prop. 5.12, p. 248), for $p$ odd: the Hilbert
pairing defined by a local Artin map satisfies (a) (exponent $i$), (b) for $1 \le i \le p-1$ and (c) on the
$\eta_i = 1 - \lambda^i$, and is skew-symmetric, provided the $\eta_k$ with $k \ge p+1$ are $p$-th powers. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Prop. 5.12, p. 248 (existence on generators, Artin-map symbol)"]
theorem hilbertPairing_isExplicitPairing (hζ : IsPrimitiveRoot ζ p) (hφ : IsLocalArtinMap φ) (hp2 : p ≠ 2) {lam : Kˣ} {eta : ℕ → Kˣ}
    (heta : ∀ i, 1 ≤ i → (eta i : K) = 1 - (lam : K) ^ i) (hpow : ∀ k, p + 1 ≤ k → ∃ β : Kˣ, β ^ p = eta k) :
    IsExplicitPairing (hilbertPairing hζ hφ) p lam eta (hilbertPairing hζ hφ (eta p) lam) (fun i _ => i) :=
  (hilbertPairing_isSteinberg hζ hφ).isExplicitPairing heta (Fact.out) hp2 hpow

end NumberFieldKB.MilneCFT.Ch8
