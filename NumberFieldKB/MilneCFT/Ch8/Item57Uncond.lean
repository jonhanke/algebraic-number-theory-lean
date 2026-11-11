import NumberFieldKB.MilneCFT.Ch8.Item57Norm
import NumberFieldKB.MilneCFT.Ch8.Item57Common
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Places.Semilocal
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# Milne, *Class Field Theory*, Chapter VIII, 5.7: $(b,a)_v = (a,b)_v^{-1}$, proved

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, 5.7 (p. 246)
and Theorem 5.11 (p. 247).

Milne proves 5.7 with cyclic algebras ($A(b,a;\zeta) \cong A(a,b;\zeta)^{\mathrm{opp}}$). We use the Steinberg route
instead, with Tau Ceti's idèlic Artin map (ported under `NumberFieldKB/TauCetiPort/`):

* `kummerSymb φ γ x`: for an abelian extension $M/K$ with idèlic Artin map $\phi$, $\gamma \in M^\times$ with
  $\gamma^n \in K$ and an idèle $x$, the $\mu \in K$ with $\phi(x)\gamma = \mu\gamma$. The symbols `hilbertArtin`,
  `hilbertArtinInf` are this at the idèles $\iota_v b$ (by definition). It is multiplicative in $\gamma$ and in $x$.
* `idelicArtinTauCeti_restrict`: for a $K$-embedding $f : L \to M$ of abelian extensions, Tau Ceti's Artin map of $L$
  is the restriction of that of $M$ (Tau Ceti's `globalArtinMap_comp`). With the uniqueness of idèlic Artin maps
  (`idelicArtin_unique`), the symbols of the two Kummer extensions $K[a^{1/n}]$, $K[b^{1/n}]$ in 5.7 are computed in
  one abelian extension $M$ containing both (the splitting field of $(X^n - a)(X^n - b)$).
* `idelicArtinTauCeti_norm_fin`, `idelicArtinTauCeti_norm_inf`: a global norm $N_{E/K}(y)$, placed at one prime, has
  trivial Artin symbol (it is the product of the local norms from the primes of $E$ above it; Tau Ceti's
  `algebraMap_norm_eq_prod_norm`, `normGroup_le_ker_localArtinAt` and their archimedean analogues).
* `exists_norm_eq_neg`: $-\gamma^n$ is a norm from $K(\gamma)$ (the minimal polynomial of $\gamma$ is
  $X^d - \gamma^d$, $d = [K(\gamma):K]$ divides $n$; parity of $n/d$). Hence $(\gamma, -\gamma^n) = 1$.
* Expanding $(\gamma_a\gamma_b, -ab) = 1$ by bimultiplicativity gives $(a,b)(b,a) = 1$: `item5_7`, and the power
  reciprocity law without the hypothesis 5.7: `theorem_5_11_uncond`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.MilneCFT Polynomial
open scoped IsMulCommutative AdicCompletionExtension NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace Item57

variable {K : Type} [Field K] [NumberField K]

/-! ## The Kummer symbol of an element and an idèle -/

section Symb

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

open Classical in
/-- The Kummer symbol: for an idèle $x$ and $\gamma \in L$, the $\mu \in K$ with $\phi(x)\gamma = \mu\gamma$ ($1$ if
there is none). -/
def kummerSymb (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (γ : L) (x : IdeleGroup (𝓞 K) K) : K :=
  if h : ∃ μ : K, φ x γ = algebraMap K L μ * γ then h.choose else 1

theorem hilbertArtin_eq_kummerSymb (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (v : HeightOneSpectrum (𝓞 K))
    (b : Kˣ) : hilbertArtin L φ α v b =
      kummerSymb φ α (IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (algebraMap K _).toMonoidHom b)) := rfl

theorem hilbertArtinInf_eq_kummerSymb (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (α : L) (w : InfinitePlace K)
    (b : Kˣ) : hilbertArtinInf L φ α w b =
      kummerSymb φ α (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)) := rfl

theorem kummerSymb_eq (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) {γ : L} (hγ : γ ≠ 0) (x : IdeleGroup (𝓞 K) K) (μ : K)
    (h : φ x γ = algebraMap K L μ * γ) : kummerSymb φ γ x = μ :=
  dite_choose_eq L hγ _ μ h

variable {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
include hn hζ

theorem kummerSymb_spec (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) {γ : L} (hγ : γ ≠ 0) {c : K}
    (hc : γ ^ n = algebraMap K L c) (x : IdeleGroup (𝓞 K) K) :
    φ x γ = algebraMap K L (kummerSymb φ γ x) * γ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact hγ (pow_eq_zero_iff hn.ne' |>.1 hc)
  obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ c hc0 L γ hc (φ x)
  rw [kummerSymb_eq φ hγ x _ hj]
  exact hj

theorem kummerSymb_mul_right (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) {γ : L} (hγ : γ ≠ 0) {c : K}
    (hc : γ ^ n = algebraMap K L c) (x y : IdeleGroup (𝓞 K) K) :
    kummerSymb φ γ (x * y) = kummerSymb φ γ x * kummerSymb φ γ y := by
  have hx := kummerSymb_spec hn hζ φ hγ hc x
  have hy := kummerSymb_spec hn hζ φ hγ hc y
  refine kummerSymb_eq φ hγ _ _ ?_
  rw [map_mul, AlgEquiv.mul_apply, hy, map_mul, AlgEquiv.commutes, hx, map_mul]
  ring

theorem kummerSymb_mul_left (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) {γ δ : L} (hγ : γ ≠ 0) (hδ : δ ≠ 0) {c d : K}
    (hc : γ ^ n = algebraMap K L c) (hd : δ ^ n = algebraMap K L d) (x : IdeleGroup (𝓞 K) K) :
    kummerSymb φ (γ * δ) x = kummerSymb φ γ x * kummerSymb φ δ x := by
  refine kummerSymb_eq φ (mul_ne_zero hγ hδ) _ _ ?_
  rw [map_mul (φ x), kummerSymb_spec hn hζ φ hγ hc x, kummerSymb_spec hn hζ φ hδ hd x, map_mul]
  ring

/-- Transport along a $K$-embedding $f : L \to M$ when the Artin map of $L$ is the restriction of that of $M$. -/
theorem kummerSymb_map {M : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (f : L →ₐ[K] M) (φL : IdeleGroup (𝓞 K) K →* Gal(L/K)) (φM : IdeleGroup (𝓞 K) K →* Gal(M/K))
    {γ : L} (hγ : γ ≠ 0) {c : K} (hc : γ ^ n = algebraMap K L c) (x : IdeleGroup (𝓞 K) K)
    (hx : φL x = f.restrictNormalHom (φM x)) :
    kummerSymb φL γ x = kummerSymb φM (f γ) x := by
  have hfγ : f γ ≠ 0 := (map_ne_zero f).2 hγ
  have h1 := kummerSymb_spec hn hζ φL hγ hc x
  rw [hx] at h1
  have h2 := congrArg f h1
  rw [AlgHom.restrictNormalHom_commutes, map_mul, AlgHom.commutes] at h2
  exact (kummerSymb_eq φM hfγ x _ h2).symm

end Symb

/-! ## Tau Ceti's Artin map: restriction and norms -/

section TauCeti

/-- Tau Ceti's idèlic Artin map of $L$ is the restriction of that of $M$ along a $K$-embedding $L \to M$. -/
theorem idelicArtinTauCeti_restrict {L M : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M] (f : L →ₐ[K] M) (x : IdeleGroup (𝓞 K) K) :
    idelicArtinTauCeti L x = f.restrictNormalHom (idelicArtinTauCeti M x) := by
  apply Abelianization.of_injective
  rw [idelicArtinTauCeti_apply,
    TauCeti.ClassFieldTheory.of_ideleClassArtinMap K L ((IsSepClosed.lift : M →ₐ[K] _).comp f),
    ← TauCeti.ClassFieldTheory.globalArtinMap_comp K M f, ← Abelianization.map_of, of_idelicArtinTauCeti]
  rfl

variable (E : Type) [Field E] [NumberField E] [Algebra K E] [IsAbelianGalois K E]

/-- A global norm, placed at a finite prime $v$, has trivial Artin symbol. -/
theorem idelicArtinTauCeti_norm_fin (v : HeightOneSpectrum (𝓞 K)) (y : Eˣ) :
    idelicArtinTauCeti E (IdeleGroup.ofAdicCompletion (𝓞 K) K v
      (Units.map (algebraMap K _).toMonoidHom (TauCeti.Algebra.normUnits K y))) = 1 := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  rw [idelicArtinTauCeti_eq_one_iff, TauCeti.ClassFieldTheory.globalArtinMap_local, ofMul_eq_zero]
  have hx : Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (TauCeti.Algebra.normUnits K y) =
      ∏ w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal},
        TauCeti.Algebra.normUnits (v.adicCompletion K)
          (Units.map (algebraMap E (w.1.adicCompletion E) : E →* w.1.adicCompletion E) y) := by
    refine Units.ext ?_
    simp only [Units.coe_prod, TauCeti.Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass,
      RingHom.toMonoidHom_eq_coe]
    exact TauCeti.algebraMap_norm_eq_prod_norm E v (y : E)
  rw [hx, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have := w.2
  exact TauCeti.ClassFieldTheory.normGroup_le_ker_localArtinAt v w.1 ⟨_, rfl⟩

/-- A global norm, placed at an infinite prime $w$, has trivial Artin symbol. -/
theorem idelicArtinTauCeti_norm_inf (v : InfinitePlace K) (y : Eˣ) :
    idelicArtinTauCeti E (IdeleGroup.ofCompletion (𝓞 K) K v
      (Units.map (algebraMap K _).toMonoidHom (TauCeti.Algebra.normUnits K y))) = 1 := by
  classical
  rw [idelicArtinTauCeti_eq_one_iff, TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal, ofMul_eq_zero]
  have hx : Units.map (algebraMap K v.Completion).toMonoidHom (TauCeti.Algebra.normUnits K y) =
      ∏ w : {w : InfinitePlace E // w.LiesOver v},
        TauCeti.Algebra.normUnits v.Completion
          (Units.map (algebraMap E w.1.Completion : E →* w.1.Completion) y) := by
    refine Units.ext ?_
    simp only [Units.coe_prod, TauCeti.Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass,
      RingHom.toMonoidHom_eq_coe]
    exact TauCeti.GlobalNumberFields.algebraMap_norm_eq_prod_norm_infiniteCompletion E v (y : E)
  rw [hx, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have := w.2
  exact TauCeti.ClassFieldTheory.normGroup_le_ker_infiniteLocalArtinAt v w.1 ⟨_, rfl⟩

end TauCeti

/-! ## Skew symmetry in one abelian extension -/

section Skew

variable {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
include hn hζ

variable {M : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]

/-- $(\gamma, -\gamma^n) = 1$ at a place, given that global norms placed there have trivial symbol. -/
theorem kummerSymb_neg_pow (e : Kˣ →* IdeleGroup (𝓞 K) K)
    (he : ∀ (E : IntermediateField K M) (y : Eˣ), idelicArtinTauCeti E (e (TauCeti.Algebra.normUnits K y)) = 1)
    {γ : M} (hγ : γ ≠ 0) (c : Kˣ) (hc : γ ^ n = algebraMap K M c) :
    kummerSymb (idelicArtinTauCeti M) γ (e (-c)) = 1 := by
  set E := IntermediateField.adjoin K {γ}
  obtain ⟨y, hy⟩ := exists_norm_eq_neg hn hζ hγ hc
  have hyu : TauCeti.Algebra.normUnits K y = -c := Units.ext (by simpa using hy)
  have h1 := he E y
  rw [hyu, idelicArtinTauCeti_restrict E.val] at h1
  have h2 := E.val.restrictNormalHom_commutes (idelicArtinTauCeti M (e (-c)))
    (IntermediateField.AdjoinSimple.gen K γ)
  rw [h1] at h2
  refine kummerSymb_eq _ hγ _ 1 ?_
  rw [map_one, one_mul]
  simpa using h2.symm

/-- Skew symmetry $(\delta, a)(\gamma, b) = 1$ for $\gamma^n = a$, $\delta^n = b$ in one abelian extension. -/
theorem kummerSymb_skew (e : Kˣ →* IdeleGroup (𝓞 K) K)
    (he : ∀ (E : IntermediateField K M) (y : Eˣ), idelicArtinTauCeti E (e (TauCeti.Algebra.normUnits K y)) = 1)
    {γ δ : M} (a b : Kˣ) (hγ : γ ^ n = algebraMap K M a) (hδ : δ ^ n = algebraMap K M b) :
    kummerSymb (idelicArtinTauCeti M) δ (e a) * kummerSymb (idelicArtinTauCeti M) γ (e b) = 1 := by
  have hne : ∀ {x : M} (u : Kˣ), x ^ n = algebraMap K M u → x ≠ 0 := fun {x} u hx h0 => by
    rw [h0, zero_pow hn.ne', eq_comm, map_eq_zero] at hx
    exact u.ne_zero hx
  have hγ0 := hne a hγ
  have hδ0 := hne b hδ
  have hγδ : (γ * δ) ^ n = algebraMap K M ((a * b : Kˣ) : K) := by
    rw [mul_pow, hγ, hδ, Units.val_mul, map_mul]
  have mr : ∀ {x : M} (u : Kˣ), x ^ n = algebraMap K M u → ∀ s t : Kˣ,
      kummerSymb (idelicArtinTauCeti M) x (e (s * t)) =
        kummerSymb (idelicArtinTauCeti M) x (e s) * kummerSymb (idelicArtinTauCeti M) x (e t) :=
    fun {x} u hx s t => by rw [map_mul]; exact kummerSymb_mul_right hn hζ _ (hne u hx) hx _ _
  have h0 := kummerSymb_neg_pow hn hζ e he (mul_ne_zero hγ0 hδ0) (a * b) hγδ
  rw [kummerSymb_mul_left hn hζ _ hγ0 hδ0 hγ hδ] at h0
  have h1 : kummerSymb (idelicArtinTauCeti M) γ (e (-(a * b))) = kummerSymb (idelicArtinTauCeti M) γ (e b) := by
    rw [← neg_mul, mr a hγ, kummerSymb_neg_pow hn hζ e he hγ0 a hγ, one_mul]
  have h2 : kummerSymb (idelicArtinTauCeti M) δ (e (-(a * b))) = kummerSymb (idelicArtinTauCeti M) δ (e a) := by
    rw [← mul_neg, mr b hδ, kummerSymb_neg_pow hn hζ e he hδ0 b hδ, mul_one]
  rw [h1, h2] at h0
  rw [mul_comm]
  exact h0

end Skew

end Item57

open Item57

variable {K : Type} [Field K] [NumberField K]

/-- **5.7, proved** (Milne, *CFT*, VIII, 5.7, p. 246): for $n \ge 1$ and $K \ni \zeta_n$,
$(b,a)_v = (a,b)_v^{-1}$ at every finite and every infinite prime. -/
@[kb "milne2020cft" "Ch. VIII, 5.7, p. 246 (proved)"]
theorem item5_7 (n : ℕ) : Item5_7 K n := by
  refine ⟨fun hn ζ hζ La _ _ _ _ Lb _ _ _ _ a b α β hα hβ hαg hβg φa φb hφa hφb hφaK hφbK => ?_⟩
  obtain ⟨M, _, _, _, _, ⟨fa⟩, ⟨fb⟩⟩ := exists_common hn hζ La Lb a b α β hα hβ hαg hβg
  obtain rfl : φa = idelicArtinTauCeti La :=
    idelicArtin_unique La φa _ hφa (isIdelicArtinMap_tauCeti La) hφaK (idelicArtinTauCeti_principal La)
  obtain rfl : φb = idelicArtinTauCeti Lb :=
    idelicArtin_unique Lb φb _ hφb (isIdelicArtinMap_tauCeti Lb) hφbK (idelicArtinTauCeti_principal Lb)
  have hne : ∀ {L : Type} [Field L] [Algebra K L] {x : L} (u : Kˣ), x ^ n = algebraMap K L u → x ≠ 0 :=
    fun {L} _ _ {x} u hx h0 => by
      rw [h0, zero_pow hn.ne', eq_comm, map_eq_zero] at hx
      exact u.ne_zero hx
  have key : ∀ e : Kˣ →* IdeleGroup (𝓞 K) K,
      (∀ (E : IntermediateField K M) (y : Eˣ), idelicArtinTauCeti E (e (TauCeti.Algebra.normUnits K y)) = 1) →
      kummerSymb (idelicArtinTauCeti Lb) β (e a) * kummerSymb (idelicArtinTauCeti La) α (e b) = 1 := by
    intro e he
    rw [kummerSymb_map hn hζ fb _ _ (hne b hβ) hβ (e a) (idelicArtinTauCeti_restrict fb _),
      kummerSymb_map hn hζ fa _ _ (hne a hα) hα (e b) (idelicArtinTauCeti_restrict fa _)]
    exact kummerSymb_skew hn hζ e he a b (by rw [← map_pow, hα, AlgHom.commutes])
      (by rw [← map_pow, hβ, AlgHom.commutes])
  refine ⟨fun v => ?_, fun w => ?_⟩
  · exact key ((IdeleGroup.ofAdicCompletion (𝓞 K) K v).comp (Units.map (algebraMap K _).toMonoidHom))
      (fun E y => idelicArtinTauCeti_norm_fin E v y)
  · exact key ((IdeleGroup.ofCompletion (𝓞 K) K w).comp (Units.map (algebraMap K _).toMonoidHom))
      (fun E y => idelicArtinTauCeti_norm_inf E w y)

/-- **Theorem 5.11, the power reciprocity law, unconditional** (Milne, *CFT*, VIII, Theorem 5.11, p. 247, with the
erratum recorded at `theorem_5_11`): `theorem_5_11` with its hypothesis 5.7 discharged by `item5_7`. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.11, p. 247 (power reciprocity law, unconditional)"]
theorem theorem_5_11_uncond (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
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
      (∏ᶠ v ∈ Sset n (∅ : Set K), hilbertArtin Lb φb β v a) * ∏ w : InfinitePlace K, hilbertArtinInf Lb φb β w a :=
  theorem_5_11 n hn ζ hζ (item5_7 n) La Lb a b α β hα hβ hαg hβg φa φb hφa hφb hφaK hφbK hS

end NumberFieldKB.MilneCFT.Ch8
