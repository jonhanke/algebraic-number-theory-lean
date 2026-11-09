import NumberFieldKB.MilneCFT.LubinTate.ArtinMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The local Kronecker–Weber theorem (Milne, *Class Field Theory*, Chapter I, §4)

## Ramification groups
For a finite Galois extension $L/K$ inside $\Omega$ with $G = \mathrm{Gal}(L/K)$, $\mathcal O_L$ = `integers L` and
$\mathfrak m_L$ = `maxIdealL L` (the radical of $\mathfrak m_K\mathcal O_L$, which is the maximal ideal of
$\mathcal O_L$ since $\mathfrak m_K\mathcal O_L = \mathfrak m_L^e$):
* `ramificationGroup L i` $= G_i = \{\sigma : \mathrm{ord}_L(\sigma a - a) \ge i+1 \ \forall a \in \mathcal O_L\}$
  (lower numbering, $i \ge 0$; Milne extends to real $u \ge -1$ by $G_u = G_{\lceil u\rceil}$, `ramificationGroupReal`);
* `herbrandPhi L` $= \varphi$, $\varphi(u) = \int_0^u dt/(G_0 : G_t)$;
* `upperRamificationGroup L v` $= G^v = G_{\psi(v)}$, $\psi = \varphi^{-1}$;
* `IsJump` (Definition 4.5).

## Statements
* Named statements: Proposition 4.1 (`LubinTateLowerFiltration`), Proposition 4.3 (`LubinTateUpperFiltration`),
  Proposition 4.4 (`HerbrandQuotient`), Theorem 4.6 (`HasseArf`), Theorem 4.8 (`LocalKroneckerWeber`), Lemmas 4.9,
  4.10, 4.11, Corollary 4.12 (`LocalKroneckerWeberQp`), Theorem 4.16 (`KroneckerWeber`), Lemma 4.17
  (`InertiaGeneration`).
* Example 4.2 is a computation for $K_{\pi,n}$ stated as `LubinTateHerbrand` (named; the values
  $\varphi(q^i - 1) = i$).

Example 4.7 (`LubinTate/Jumps.lean`), Example 4.13 and the upper numbering on an infinite Galois extension (p. 46)
are in `LubinTate/Complements.lean` and `LubinTate/Jumps.lean`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Ramification groups (lower numbering) -/

/-- The maximal ideal $\mathfrak m_L$ of $\mathcal O_L$: the radical of $\mathfrak m_K\mathcal O_L$. -/
def maxIdealL (L : IntermediateField K Ω) : Ideal (integers L) :=
  ((𝓂[K]).map (algebraMap 𝒪[K] (integers L))).radical

theorem galMap_mem_integers (L : IntermediateField K Ω) (σ : Gal(L/K)) {a : L} (ha : a ∈ integers L) :
    σ a ∈ integers L := by
  have : IsIntegral 𝒪[K] a := ha
  exact this.map (σ.toAlgHom.restrictScalars 𝒪[K])

/-- The restriction of a Galois automorphism to $\mathcal O_L$. -/
def galRestrictInt (L : IntermediateField K Ω) (σ : Gal(L/K)) : integers L →+* integers L where
  toFun a := ⟨σ a, galMap_mem_integers L σ a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem galRestrict_map_maxIdealL_le (L : IntermediateField K Ω) (σ : Gal(L/K)) :
    (maxIdealL L).map (galRestrictInt L σ) ≤ maxIdealL L := by
  have hc : (galRestrictInt L σ).comp (algebraMap 𝒪[K] (integers L)) = algebraMap 𝒪[K] (integers L) := by
    refine RingHom.ext fun r => Subtype.ext ?_
    show σ (algebraMap 𝒪[K] L r) = algebraMap 𝒪[K] L r
    have : algebraMap 𝒪[K] L r = algebraMap K L (r : K) := rfl
    rw [this]; exact σ.commutes _
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  have : (galRestrictInt L σ x) ^ k = galRestrictInt L σ (x ^ k) := by simp
  show (galRestrictInt L σ x) ^ k ∈ _
  rw [this]
  have h' : Ideal.map (galRestrictInt L σ) ((𝓂[K]).map (algebraMap 𝒪[K] (integers L))) ≤
      (𝓂[K]).map (algebraMap 𝒪[K] (integers L)) := by
    rw [Ideal.map_map, hc]
  exact h' (Ideal.mem_map_of_mem _ hk)

theorem galRestrict_pow_mem (L : IntermediateField K Ω) (σ : Gal(L/K)) (m : ℕ) {b : integers L}
    (hb : b ∈ maxIdealL L ^ m) : galRestrictInt L σ b ∈ maxIdealL L ^ m := by
  have h1 : Ideal.map (galRestrictInt L σ) (maxIdealL L ^ m) ≤ maxIdealL L ^ m := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono (galRestrict_map_maxIdealL_le L σ) m
  exact h1 (Ideal.mem_map_of_mem _ hb)

/-- **The $i$-th ramification group** $G_i$ (Milne, *CFT*, I, §4, p. 44; *ANT* 7.57), $i \ge 0$: the
$\sigma \in \mathrm{Gal}(L/K)$ with $\sigma a - a \in \mathfrak m_L^{i+1}$ for all $a \in \mathcal O_L$
($\mathrm{ord}_L(\sigma a - a) \ge i + 1$). $G_0$ is the inertia group. -/
@[kb "milne2020cft" "Ch. I, §4 (ramification groups G_i, lower numbering)"]
def ramificationGroup (L : IntermediateField K Ω) [FiniteDimensional K L] (i : ℕ) : Subgroup Gal(L/K) where
  carrier := {σ | ∀ a ∈ integers L, ∃ b ∈ maxIdealL L ^ (i + 1), (b : L) = σ a - a}
  mul_mem' := by
    intro σ τ hσ hτ a ha
    obtain ⟨b, hb, hba⟩ := hτ a ha
    obtain ⟨c, hc, hca⟩ := hσ a ha
    refine ⟨galRestrictInt L σ b + c, Ideal.add_mem _ (galRestrict_pow_mem L σ _ hb) hc, ?_⟩
    have : ((galRestrictInt L σ b : integers L) : L) = σ b := rfl
    simp only [Subalgebra.coe_add, this, hba, hca, map_sub]
    simp [AlgEquiv.mul_apply]
  one_mem' := by
    intro a ha
    exact ⟨0, Ideal.zero_mem _, by simp⟩
  inv_mem' := by
    intro σ hσ a ha
    have hc : σ⁻¹ a ∈ integers L := galMap_mem_integers L σ⁻¹ ha
    obtain ⟨b, hb, hba⟩ := hσ _ hc
    refine ⟨-b, (Ideal.neg_mem_iff _).2 hb, ?_⟩
    have : σ (σ⁻¹ a) = a := by simp
    simp only [Subalgebra.coe_neg, hba, this]
    ring

/-- $G_u = G_{\lceil u\rceil}$ for real $u$ (Milne, *CFT*, I, §4, p. 45), with $G_u = G_0$ for $-1 < u \le 0$ and
$G_{-1} = G$. -/
def ramificationGroupReal (L : IntermediateField K Ω) [FiniteDimensional K L] (u : ℝ) : Subgroup Gal(L/K) :=
  if u ≤ -1 then ⊤ else ramificationGroup L ⌈u⌉₊

/-- **The Herbrand function** $\varphi$ (Milne, *CFT*, I, §4, p. 46): the continuous piecewise linear function with
$\varphi(0) = 0$ and $\varphi'(u) = (G_0 : G_u)^{-1}$ for $u$ not an integer, i.e.
$\varphi(u) = \int_0^u (G_0 : G_t)^{-1}\,dt$. -/
@[kb "milne2020cft" "Ch. I, §4 (the Herbrand function φ)"]
def herbrandPhi (L : IntermediateField K Ω) [FiniteDimensional K L] (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, 1 / ((ramificationGroupReal L t).relIndex (ramificationGroup L 0) : ℝ)

/-- **Upper numbering** $G^v = G_{\varphi^{-1}(v)}$ (Milne, *CFT*, I, §4, p. 46), for $v \ge 0$: $\varphi^{-1}(v)$ is
the least $u \ge 0$ with $\varphi(u) \ge v$ ($\varphi$ is continuous and increasing). -/
@[kb "milne2020cft" "Ch. I, §4 (upper numbering G^v)"]
def upperRamificationGroup (L : IntermediateField K Ω) [FiniteDimensional K L] (v : ℝ) : Subgroup Gal(L/K) :=
  ramificationGroupReal L (sInf {u : ℝ | 0 ≤ u ∧ v ≤ herbrandPhi L u})

/-- **Definition 4.5** (Milne, *CFT*, I): $v$ is a jump in the filtration $(G^v)$ if $G^v \ne G^{v+\varepsilon}$ for
every $\varepsilon > 0$. -/
@[kb "milne2020cft" "Ch. I, Definition 4.5"]
def IsJump (L : IntermediateField K Ω) [FiniteDimensional K L] (v : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → upperRamificationGroup L v ≠ upperRamificationGroup L (v + ε)

/-! ## The ramification groups of $K_{\pi,n}/K$ -/

/-- $U^{(i)}/U^{(n)} \subseteq (A/\mathfrak m^n)^\times$: the classes of units $\equiv 1 \pmod{\mathfrak m^i}$
(Milne, *CFT*, I, §4, p. 45; $U^{(0)} = U$). -/
def unitFiltrationMod (n i : ℕ) : Subgroup (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ where
  carrier := {x | ∃ u : 𝒪[K]ˣ, Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u = x ∧
    (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ i}
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    refine ⟨u * v, by simp, ?_⟩
    have : ((u * v : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((u : 𝒪[K]) - 1) * v + ((v : 𝒪[K]) - 1) := by
      simp; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hu) hv
  one_mem' := ⟨1, by simp, by simp⟩
  inv_mem' := by
    rintro _ ⟨u, rfl, hu⟩
    refine ⟨u⁻¹, by simp, ?_⟩
    have : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1 = -(((u : 𝒪[K]) - 1) * ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) := by
      have h : (u : 𝒪[K]) * ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) = 1 := by simp
      linear_combination h
    rw [this]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hu)

variable (K Ω) in
/-- **Proposition 4.1** (named statement; Milne, *CFT*, I, Proposition 4.1): for $L = K_{\pi,n}$ and the isomorphism
$\chi : (A/\mathfrak m^n)^\times \to G$ of Theorem 3.6, $\chi(U^{(i)}/U^{(n)}) = G_{q^i - 1}$ ($0 \le i \le n$); and
(from the proof) for $1 \le i < n$ and $u \in U^{(i)} \setminus U^{(i+1)}$, $\chi(u) \notin G_{q^i}$. -/
@[kb "milne2020cft" "Ch. I, Proposition 4.1 (input)"]
structure LubinTateLowerFiltration (h : LubinTateExtensionTheorem K Ω) : Prop where
  map_eq : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (_ : 1 ≤ n)
    (χ : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ ≃* Gal(ltField Ω π n/K)),
    (∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π n),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u) ⟨α, mem_ltField hα⟩ : ltField Ω π n) : Ω) =
        ltAct hπ n u α) →
    ∀ i ≤ n, (unitFiltrationMod n i).map χ.toMonoidHom = ramificationGroup (ltField Ω π n) (resCard K ^ i - 1)
  not_mem : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (_ : 1 ≤ n)
    (χ : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ ≃* Gal(ltField Ω π n/K)),
    (∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π n),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u) ⟨α, mem_ltField hα⟩ : ltField Ω π n) : Ω) =
        ltAct hπ n u α) →
    ∀ i, 1 ≤ i → i < n → ∀ x ∈ unitFiltrationMod n i, x ∉ unitFiltrationMod n (i + 1) →
      χ x ∉ ramificationGroup (ltField Ω π n) (resCard K ^ i)

variable (K Ω) in
/-- **Example 4.2** (named statement; Milne, *CFT*, I, Example 4.2): for $L = K_{\pi,n}$,
$\varphi(q^i - 1) = i$ for $0 \le i \le n$, hence $G^i = G_{q^i - 1}$. -/
@[kb "milne2020cft" "Ch. I, Example 4.2 (input)"]
structure LubinTateHerbrand : Prop where
  phi_eq : ∀ {π : 𝒪[K]}, Irreducible π → ∀ n i : ℕ, 1 ≤ n → i ≤ n →
    herbrandPhi (ltField Ω π n) ((resCard K : ℝ) ^ i - 1) = i
  upper_eq : ∀ {π : 𝒪[K]}, Irreducible π → ∀ n i : ℕ, 1 ≤ n → i ≤ n →
    upperRamificationGroup (ltField Ω π n) i = ramificationGroup (ltField Ω π n) (resCard K ^ i - 1)

variable (K Ω) in
/-- **Proposition 4.3** (named statement; Milne, *CFT*, I, Proposition 4.3): under $\chi$,
$U^{(i)}/U^{(n)} \mapsto G^i$. -/
@[kb "milne2020cft" "Ch. I, Proposition 4.3 (input)"]
structure LubinTateUpperFiltration : Prop where
  map_eq : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (_ : 1 ≤ n)
    (χ : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ ≃* Gal(ltField Ω π n/K)),
    (∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π n),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u) ⟨α, mem_ltField hα⟩ : ltField Ω π n) : Ω) =
        ltAct hπ n u α) →
    ∀ i ≤ n, (unitFiltrationMod n i).map χ.toMonoidHom = upperRamificationGroup (ltField Ω π n) i

/-- **Proposition 4.3 from Proposition 4.1 and Example 4.2** (Milne: "immediate consequence of (4.1) and (4.2)"). -/
theorem lubinTateUpperFiltration_of (h : LubinTateExtensionTheorem K Ω)
    (h41 : LubinTateLowerFiltration K Ω h) (h42 : LubinTateHerbrand K Ω) :
    LubinTateUpperFiltration K Ω := by
  refine ⟨fun hπ n hn χ hχ i hi => ?_⟩
  rw [h41.map_eq hπ n hn χ hχ i hi, h42.upper_eq hπ n i hn hi]

variable (K Ω) in
/-- **Proposition 4.4 (Herbrand)** (named statement; Milne, *CFT*, I, Proposition 4.4; Serre, *Local Fields*,
IV.3, Proposition 14): for finite Galois $M \supseteq L \supseteq K$, $(G/H)^v = G^vH/H$, i.e. restriction maps
$\mathrm{Gal}(M/K)^v$ onto $\mathrm{Gal}(L/K)^v$.

**Proved here** as `herbrandQuotient` (`LubinTate/HerbrandTauCeti.lean`), from the ported Tau Ceti
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`
(`TauCeti/NumberTheory/LocalField/Herbrand/UpperQuotient.lean`), through `upperRamificationGroup_eq` (our upper
ramification group inside `Ω` is Tau Ceti's, for Tau Ceti's local-field structure on the intermediate field). -/
@[kb "milne2020cft" "Ch. I, Proposition 4.4"]
structure HerbrandQuotient : Prop where
  map_eq : ∀ (L M : IntermediateField K Ω) [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L]
    [IsGalois K M] (h : L ≤ M) (v : ℝ), 0 ≤ v →
    (upperRamificationGroup M v).map (galRestrict h) = upperRamificationGroup L v

variable (K Ω) in
/-- **Theorem 4.6 (Hasse–Arf)** (named statement; Milne, *CFT*, I, Theorem 4.6; Serre, *Local Fields*, V.7): if
$L/K$ is finite abelian, the jumps of the upper filtration are integers: if $G_i \ne G_{i+1}$ then
$\varphi(i) \in \mathbb Z$.

**Proved here** as `hasseArf` (`LubinTate/HasseArfTauCeti.lean`), from the ported Tau Ceti
`TauCeti.LocalFieldsRamification.hasseArf` (`TauCeti/NumberTheory/LocalField/Herbrand/HasseArf/Abelian.lean`, integrality
of the upper breaks), through `upperJump_herbrand_iff` and the comparisons of `LubinTate/HerbrandTauCeti.lean`. Also
proved in Yamaguchi (`n-yamaguchi-0729/ClassFieldTheory`) `ClassFieldTheory.hasseArf`
(`Nyll/ClassFieldTheory/Theorems/HasseArf/HasseArf.lean:40`) at Yamaguchi commit `fbd320c` (not used). -/
@[kb "milne2020cft" "Ch. I, Theorem 4.6 (input)"]
structure HasseArf : Prop where
  integral : ∀ (L : FiniteAbelianExt K Ω) (i : ℕ), ramificationGroup L.toField i ≠ ramificationGroup L.toField (i + 1) →
    ∃ k : ℤ, herbrandPhi L.toField i = k

/-! ## The local Kronecker–Weber theorem -/

variable (K Ω) in
/-- **Theorem 4.8 (local Kronecker–Weber)** (named statement; Milne, *CFT*, I, Theorem 4.8): for every prime element
$\pi$, $K_\pi K^{\mathrm{un}} = K^{\mathrm{ab}}$: every finite abelian extension of $K$ lies in
$K_\pi K^{\mathrm{un}}$. -/
@[kb "milne2020cft" "Ch. I, Theorem 4.8 (input)"]
structure LocalKroneckerWeber : Prop where
  le : ∀ {π : 𝒪[K]}, Irreducible π → ∀ L : FiniteAbelianExt K Ω, L.toField ≤ ltTower Ω π ⊔ unramifiedClosure K Ω

/-- The ramification index $e(L/K)$ of a finite extension: the ramification index of $\mathfrak m_L$ over
$\mathfrak m_K$ (Mathlib's `Ideal.ramificationIdx`). -/
def ramIdx (L : IntermediateField K Ω) : ℕ := Ideal.ramificationIdx (maxIdealL L) 𝒪[K]

variable (K Ω) in
/-- **Lemma 4.9** (named statement; Milne, *CFT*, I, Lemma 4.9): let $L$ be an abelian totally ramified extension of
$K$ (possibly infinite: every finite subextension is totally ramified). If $L \supseteq K_\pi$, then $L = K_\pi$. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.9 (input)"]
structure LubinTateTotallyRamified : Prop where
  eq : ∀ {π : 𝒪[K]}, Irreducible π → ∀ L : IntermediateField K Ω, IsGalois K L →
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) →
    (∀ M : IntermediateField K Ω, M ≤ L → FiniteDimensional K M → IsTotallyRamifiedExt M) →
    ltTower Ω π ≤ L → L = ltTower Ω π

variable (K Ω) in
/-- **Lemma 4.10** (named statement; Milne, *CFT*, I, Lemma 4.10): every finite unramified extension of $K_\pi$ is
contained in $K_\pi K^{\mathrm{un}}$. By Milne's footnote such an extension is $K_\pi L'$ with $L'$ a finite
unramified extension of some $K_{\pi,n}$; "$L'/K_{\pi,n}$ unramified" is $e(L'/K) = e(K_{\pi,n}/K)$. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.10 (input)"]
structure LubinTateUnramified : Prop where
  le : ∀ {π : 𝒪[K]}, Irreducible π → ∀ (n : ℕ) (L' : IntermediateField K Ω), FiniteDimensional K L' →
    ltField Ω π n ≤ L' → ramIdx L' = ramIdx (ltField Ω π n) → L' ≤ ltTower Ω π ⊔ unramifiedClosure K Ω

variable (K Ω) in
/-- **Lemma 4.11** (named statement; Milne, *CFT*, I, Lemma 4.11): if $L$ is a finite abelian extension of $K$ of
exponent $m$ and $K_m$ is the unramified extension of degree $m$, there is a totally ramified abelian extension $L_t$
of $K$ with $L K_m = L_t K_m$. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.11 (input)"]
structure ExponentDecomposition : Prop where
  exists_totallyRamified : ∀ (L : FiniteAbelianExt K Ω) (m : ℕ), (∀ σ : Gal(L.toField/K), σ ^ m = 1) →
    ∀ Km : FiniteAbelianExt K Ω, IsUnramifiedExt Km.toField → Module.finrank K Km.toField = m →
    ∃ Lt : FiniteAbelianExt K Ω, IsTotallyRamifiedExt Lt.toField ∧ L.toField ⊔ Km.toField = Lt.toField ⊔ Km.toField

/-! ## $\mathbb Q_p$ and $\mathbb Q$ -/

/-- **Corollary 4.12 (local Kronecker–Weber for $\mathbb Q_p$)** (named statement; Milne, *CFT*, I, Corollary 4.12):
every finite abelian extension of $\mathbb Q_p$ is contained in a cyclotomic extension $\mathbb Q_p[\zeta_n]$.

**Proved elsewhere** (recorded, not imported): Yamaguchi
(`n-yamaguchi-0729/ClassFieldTheory`) `KroneckerWeber.exists_localCyclotomicEmbedding`
(`Nyll/ClassFieldTheory/KroneckerWeber/LocalCyclotomicEmbedding.lean:195`) at Yamaguchi commit `fbd320c`. Needed to
apply it here: Yamaguchi's conclusion is stronger (it also gives a primitive root generating the field and the exact
value of the order); one must check that its cyclotomic field over the p-adic numbers is the same type as ours.

**Proved here** as `localKroneckerWeberQp` (`LubinTate/KroneckerWeberYamaguchi.lean`), from the
ported Yamaguchi theorem (`NumberFieldKB/YamaguchiPort/`); the cyclotomic field there is Mathlib's
`CyclotomicField m ℚ_[p]`, the same type. -/
@[kb "milne2020cft" "Ch. I, Corollary 4.12 (input)"]
structure LocalKroneckerWeberQp (p : ℕ) [Fact p.Prime] : Prop where
  le_cyclotomic : ∀ (L : Type) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L],
    (∀ σ τ : Gal(L/ℚ_[p]), σ * τ = τ * σ) → ∃ n : ℕ, 0 < n ∧ Nonempty (L →ₐ[ℚ_[p]] CyclotomicField n ℚ_[p])

/-- **Theorem 4.16 (Kronecker–Weber)** (named statement; Milne, *CFT*, I, Theorem 4.16): every finite abelian
extension of $\mathbb Q$ is contained in a cyclotomic extension $\mathbb Q[\zeta_n]$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.kroneckerWeber` (`TauCeti/NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean:178`)
at Tau Ceti commit `7ed979dc`. Needed to apply it here: the statements have the same shape; Tau Ceti assumes
Mathlib's abelian Galois extension condition, while ours assumes a Galois extension with commuting Galois group. -/
@[kb "milne2020cft" "Ch. I, Theorem 4.16 (input)"]
structure KroneckerWeber : Prop where
  le_cyclotomic : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : Gal(L/ℚ), σ * τ = τ * σ) → ∃ n : ℕ, 0 < n ∧ Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ)

/-- **Lemma 4.17** (named statement; Milne, *CFT*, I, Lemma 4.17): for a finite Galois extension $L$ of $\mathbb Q$,
$\mathrm{Gal}(L/\mathbb Q)$ is generated by the inertia groups of the primes of $L$ (only the ramified ones have
nontrivial inertia). -/
@[kb "milne2020cft" "Ch. I, Lemma 4.17 (input)"]
structure InertiaGeneration : Prop where
  closure_eq : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    Subgroup.closure (⋃ (P : Ideal (NumberField.RingOfIntegers L)) (_ : P.IsMaximal),
      (P.toAddSubgroup.inertia Gal(L/ℚ) : Set Gal(L/ℚ))) = ⊤

end NumberFieldKB.MilneCFT.LocalCFT
