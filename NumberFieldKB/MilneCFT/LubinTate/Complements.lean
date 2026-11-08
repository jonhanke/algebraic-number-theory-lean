import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.MilneCFT.LubinTate.FormalGroup
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Lubin–Tate theory: the remaining items of Chapter I, §§3–4 (Milne, *Class Field Theory*)

* **Proposition 3.10** (`LubinTateIsoOverCompletion`) and **Lemma 3.11** (`FrobeniusMinusOneSurjective`), named
  statements. Milne works over $B$, the valuation ring of the completion $\widehat{K^{\mathrm{un}}}$ of the maximal
  unramified extension, with its Frobenius $\sigma$. The completion is not a subfield of $K^{\mathrm{al}} = \Omega$, so
  $B$ enters through its characterization (`IsCompletedUnramifiedInt`): a complete discrete valuation ring over
  $A = \mathcal O_K$ in which a prime element of $A$ stays prime, whose residue field is an algebraic closure of
  $k$; and $\sigma$ is an automorphism of $B$ over $A$ inducing $x \mapsto x^q$ on the residue field.
* **Lemma 3.12** (`SubfieldsClosed`, named): every intermediate field of $K^{\mathrm{al}}/K$ is closed, for the
  topology of the (unique) extension of the valuation of $K$. Mathlib has Krasner's lemma
  (`IsKrasner.of_completeSpace`), on which the standard proof rests; Milne argues by continuity of the Galois action.
* **Example 3.13** (`CyclotomicArtinQp`, named): the local Artin map of $\mathbb Q_p$ on $\mathbb Q_p[\zeta_n]$.
* **Example 4.7** (`example_4_7`): the lower jumps of $K_{\pi,n}/K$ are among $q^k - 1$, $0 \le k < n$, where
  $\varphi$ takes the value $k$; proved from Proposition 4.1, Example 4.2 and the bounds on the ramification
  quotients recalled on p. 44 (`RamificationQuotientBounds`, named).
* **Example 4.13** (`Example413`, named): an abelian extension of $\mathbb Q_5$ that is not the compositum of a
  totally ramified and an unramified extension.
* The upper numbering on an infinite Galois extension (p. 46, `upperRamificationGroupInf`).
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Proposition 3.10 and Lemma 3.11: the completion of $K^{\mathrm{un}}$ -/

section Completion

variable (K) in
/-- **$B$ and its Frobenius** (Milne, *CFT*, I, §3, before Proposition 3.10): $B$ is the valuation ring of
$\widehat{K^{\mathrm{un}}}$ and $\sigma$ its Frobenius automorphism. Characterization used here: $B$ is a discrete
valuation ring, complete for its maximal ideal; a prime element of $A = \mathcal O_K$ is a prime element of $B$
($\widehat{K^{\mathrm{un}}}/K$ is unramified); the residue field of $B$ is algebraically closed and algebraic over $k$
(every element of $B$ is a root of a monic polynomial over $A$ modulo $\mathfrak m_B$); and $\sigma$ fixes $A$ and
induces $x \mapsto x^q$ on the residue field. -/
@[kb "milne2020cft" "Ch. I, §3, before Proposition 3.10 (B and σ)"]
structure IsCompletedUnramifiedInt (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra 𝒪[K] B] (σ : B ≃+* B) : Prop where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal B) B
  irreducible : ∀ π : 𝒪[K], Irreducible π → Irreducible (algebraMap 𝒪[K] B π)
  residue_isAlgClosed : IsAlgClosed (IsLocalRing.ResidueField B)
  residue_algebraic : ∀ b : B, ∃ P : 𝒪[K][X], P.Monic ∧ aeval b P ∈ IsLocalRing.maximalIdeal B
  frob_fix : ∀ a : 𝒪[K], σ (algebraMap 𝒪[K] B a) = algebraMap 𝒪[K] B a
  frob_mod : ∀ b : B, σ b - b ^ resCard K ∈ IsLocalRing.maximalIdeal B

variable (K) in
/-- **Lemma 3.11** (named statement; Milne, *CFT*, I, Lemma 3.11): $b \mapsto \sigma b - b : B \to B$ and
$b \mapsto \sigma b / b : B^\times \to B^\times$ are surjective, with kernels $A$ and $A^\times$. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.11 (input)"]
structure FrobeniusMinusOneSurjective : Prop where
  add_surjective : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ → ∀ c : B, ∃ b : B, σ b - b = c
  add_ker : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ → ∀ b : B, σ b - b = 0 ↔ b ∈ (algebraMap 𝒪[K] B).range
  mul_surjective : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ → ∀ c : Bˣ, ∃ b : Bˣ, Units.map σ.toMonoidHom b / b = c
  mul_ker : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ → ∀ b : Bˣ,
      Units.map σ.toMonoidHom b / b = 1 ↔ b ∈ (Units.map (algebraMap 𝒪[K] B).toMonoidHom).range

variable (K) in
/-- **Proposition 3.10** (named statement; Milne, *CFT*, I, Proposition 3.10): let $f \in \mathcal F_\pi$ and
$g \in \mathcal F_\varpi$ with $\varpi = u\pi$. Then $F_f$ and $F_g$ become $A$-isomorphic over $B$: there are
$\varepsilon \in B^\times$ with $\sigma\varepsilon = \varepsilon u$ and $\theta \in B[[T]]$ with
(a) $\theta(T) = \varepsilon T + (\deg \ge 2)$; (b) $\theta^\sigma = \theta \circ [u]_f$;
(c) $\theta(F_f(X,Y)) = F_g(\theta(X), \theta(Y))$; (d) $\theta \circ [a]_f = [a]_g \circ \theta$ for $a \in A$.
Power series over $A$ are mapped to $B[[T]]$ by `PowerSeries.map`. -/
@[kb "milne2020cft" "Ch. I, Proposition 3.10 (input)"]
structure LubinTateIsoOverCompletion : Prop where
  exists_iso : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ →
    ∀ {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) {f g : PowerSeries 𝒪[K]}
      (hf : f ∈ lubinTateSeries π (resCard K)) (hg : g ∈ lubinTateSeries ((u : 𝒪[K]) * π) (resCard K)),
    ∃ (ε : Bˣ) (θ : PowerSeries B),
      σ ε = ε * algebraMap 𝒪[K] B u ∧
      PowerSeries.constantCoeff θ = 0 ∧ PowerSeries.coeff 1 θ = ε ∧
      PowerSeries.map σ.toRingHom θ = θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
        (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf u).toPowerSeries) ∧
      θ.subst (MvPowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateFormalGroup (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf).toPowerSeries) =
        (MvPowerSeries.map (algebraMap 𝒪[K] B) (lubinTateFormalGroup
          (lubinTateHyp_of_isNonarchimedeanLocalField K ((irreducible_units_mul u).2 hπ)) hg).toPowerSeries).subst
          ![θ.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B),
            θ.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B)] ∧
      ∀ a : 𝒪[K], θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf a).toPowerSeries) =
        (PowerSeries.map (algebraMap 𝒪[K] B) (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K
          ((irreducible_units_mul u).2 hπ)) hg
            a).toPowerSeries).subst θ

end Completion

/-! ## Lemma 3.12 -/

variable (K Ω) in
/-- **Lemma 3.12** (named statement; Milne, *CFT*, I, Lemma 3.12): every subfield $E$ of $K^{\mathrm{al}}$ containing
$K$ is closed. The topology on $\Omega$ is that of a valuation extending the valuation of $K$ (`ValuativeExtension`;
such an extension is unique, so the statement quantifies over it). Milne's proof: $\mathrm{Gal}(K^{\mathrm{al}}/E)$
fixes $E$, hence by continuity its closure, so the closure is $E$ by Galois theory. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.12 (input)"]
structure SubfieldsClosed : Prop where
  isClosed : ∀ [ValuativeRel Ω] [ValuativeExtension K Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
    (E : IntermediateField K Ω), IsClosed (E : Set Ω)

/-! ## Example 3.13: the local Artin map of $\mathbb Q_p$ on cyclotomic extensions -/

/-- $p$ as an element of $\mathbb Q_p^\times$. -/
def padicPrimeUnit (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- **Example 3.13** (named statement; Milne, *CFT*, I, Example 3.13): the local Artin map
$\phi_p : \mathbb Q_p^\times \to \mathrm{Gal}(L/\mathbb Q_p)$ for $L = \mathbb Q_p[\zeta]$, $\zeta$ a primitive $n$-th
root of $1$. Write $a = u p^t$ with $u \in \mathbb Z_p^\times$ (`unitToK u`, $u \in \mathcal O_{\mathbb Q_p}^\times$).
(a) If $p \nmid n$: $L$ is unramified of degree $f$, the order of $p$ in $(\mathbb Z/n)^\times$; $\phi_p(u p^t)$ is
the $t$-th power of the Frobenius; its kernel is $\mathbb Z_p^\times \times \langle p^f\rangle$.
(b) If $n = p^r$ ($r \ge 1$): $L$ is totally ramified of degree $(p-1)p^{r-1}$; $\phi_p(u p^t)$ sends $\zeta$ to
$\zeta^{k}$ for every integer $k \ge 0$ with $k u \equiv 1 \pmod{p^r}$ (Milne: $\zeta \mapsto \zeta^{u_0^{-1}}$); its
kernel is $\{u p^m : u \equiv 1 \bmod p^r\}$.
(c) In general, $n = m p^r$ with $p \nmid m$, $L = \mathbb Q_p[\zeta_m, \zeta_{p^r}]$: $\phi_p(u p^t)$ sends $\zeta_m$
to $\zeta_m^{j}$ for every $j$ with $j \equiv p^t \pmod m$ and $\zeta_{p^r}$ to $\zeta_{p^r}^k$ for every $k$ with
$k u \equiv 1 \pmod{p^r}$. -/
@[kb "milne2020cft" "Ch. I, Example 3.13 (input)"]
structure CyclotomicArtinQp (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω]
    [IsSepClosure ℚ_[p] Ω] : Prop where
  unramified : ∀ (φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])), IsLocalArtinMap φ →
    ∀ (n : ℕ) (hn : Nat.Coprime p n) (L : FiniteAbelianExt ℚ_[p] Ω) (ζ : Ω), IsPrimitiveRoot ζ n →
    L.toField = IntermediateField.adjoin ℚ_[p] {ζ} →
    IsUnramifiedExt L.toField ∧ Module.finrank ℚ_[p] L.toField = orderOf (ZMod.unitOfCoprime p hn) ∧
    (∀ (σ : Gal(L.toField/ℚ_[p])), IsFrobenius L.toField σ →
      ∀ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ), φ L (unitToK u * padicPrimeUnit p ^ t) = σ ^ t) ∧
    ((φ L).ker : Set ℚ_[p]ˣ) = {a | ∃ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ),
      (orderOf (ZMod.unitOfCoprime p hn) : ℤ) ∣ t ∧ a = unitToK u * padicPrimeUnit p ^ t}
  totallyRamified : ∀ (φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])), IsLocalArtinMap φ →
    ∀ (r : ℕ), 1 ≤ r → ∀ (L : FiniteAbelianExt ℚ_[p] Ω) (ζ : Ω) (hζ : ζ ∈ L.toField), IsPrimitiveRoot ζ (p ^ r) →
    L.toField = IntermediateField.adjoin ℚ_[p] {ζ} →
    IsTotallyRamifiedExt L.toField ∧ Module.finrank ℚ_[p] L.toField = (p - 1) * p ^ (r - 1) ∧
    (∀ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) (k : ℕ), (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r →
      ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζ, hζ⟩ : L.toField) : Ω) = ζ ^ k) ∧
    ((φ L).ker : Set ℚ_[p]ˣ) = {a | ∃ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ),
      (u : 𝒪[ℚ_[p]]) - 1 ∈ 𝓂[ℚ_[p]] ^ r ∧ a = unitToK u * padicPrimeUnit p ^ t}
  general : ∀ (φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])), IsLocalArtinMap φ →
    ∀ (m r : ℕ) (hm : Nat.Coprime p m) (L : FiniteAbelianExt ℚ_[p] Ω) (ζm ζpr : Ω) (h1 : ζm ∈ L.toField)
      (h2 : ζpr ∈ L.toField), IsPrimitiveRoot ζm m → IsPrimitiveRoot ζpr (p ^ r) →
    L.toField = IntermediateField.adjoin ℚ_[p] {ζm, ζpr} →
    ∀ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ),
      (∀ j : ℕ, ((j : ZMod m) = ((ZMod.unitOfCoprime p hm ^ t : (ZMod m)ˣ) : ZMod m)) →
        ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζm, h1⟩ : L.toField) : Ω) = ζm ^ j) ∧
      (∀ k : ℕ, (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r →
        ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζpr, h2⟩ : L.toField) : Ω) = ζpr ^ k)

/-! ## Example 4.7: the jumps of $K_{\pi,n}/K$ -/

/-- The residue field $l = \mathcal O_L/\mathfrak m_L$ of a finite extension $L$ of $K$. -/
abbrev residueFieldL (L : IntermediateField K Ω) : Type _ := integers L ⧸ maxIdealL L

variable (K Ω) in
/-- **The ramification quotients** (named statement; Milne, *CFT*, I, §4, p. 44, recalled from *ANT* 7.57–7.58): for
a finite Galois extension $L/K$ with residue field $l$, $G_0/G_1 \hookrightarrow l^\times$ and
$G_i/G_{i+1} \hookrightarrow l$ ($i \ge 1$), so $(G_0 : G_1) \mid |l| - 1$ and $(G_i : G_{i+1}) \mid |l|$; $l$ is a
finite extension of $k$, so $|l| = q^f$; and $G_i = 1$ for $i$ large. (Milne writes $q - 1$ and $q$ for $|l| - 1$ and
$|l|$; the two agree when $L/K$ is totally ramified, the case used in Example 4.7.) -/
@[kb "milne2020cft" "Ch. I, §4, p. 44 (ramification quotients; input)"]
structure RamificationQuotientBounds : Prop where
  residue_card : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L],
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card (residueFieldL L) = resCard K ^ f
  index_zero_dvd : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L],
    (ramificationGroup L 1).relIndex (ramificationGroup L 0) ∣ Nat.card (residueFieldL L) - 1
  index_succ_dvd : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (i : ℕ), 1 ≤ i →
    (ramificationGroup L (i + 1)).relIndex (ramificationGroup L i) ∣ Nat.card (residueFieldL L)
  eventually_bot : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L],
    ∃ N : ℕ, ramificationGroup L N = ⊥

/-! ## Example 4.13 -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- **Example 4.13** (named statement; Milne, *CFT*, I, Example 4.13): a finite abelian extension of $K$ need not be
$L_t L_u$ with $L_t/K$ totally ramified and $L_u/K$ unramified. Milne's example over $\mathbb Q_5$: inside
$\mathbb Q_5[\zeta_{3120}] = \mathbb Q_5[\zeta_5, \zeta_{624}]$ there is a cyclic extension $L$ of degree $4$ whose
maximal unramified subfield has degree $2$ and which is not such a compositum. -/
@[kb "milne2020cft" "Ch. I, Example 4.13 (input)"]
structure Example413 (Ω : Type*) [Field Ω] [Algebra ℚ_[5] Ω] [IsSepClosure ℚ_[5] Ω] : Prop where
  exists_not_compositum : ∀ ζ : Ω, IsPrimitiveRoot ζ 3120 → ∃ L : FiniteAbelianExt ℚ_[5] Ω,
    L.toField ≤ IntermediateField.adjoin ℚ_[5] {ζ} ∧ Module.finrank ℚ_[5] L.toField = 4 ∧
    IsCyclic Gal(L.toField/ℚ_[5]) ∧
    ¬ ∃ Lt Lu : IntermediateField ℚ_[5] Ω, FiniteDimensional ℚ_[5] Lt ∧ FiniteDimensional ℚ_[5] Lu ∧
      IsTotallyRamifiedExt Lt ∧ IsUnramifiedExt Lu ∧ L.toField = Lt ⊔ Lu

/-! ## Upper numbering on an infinite Galois extension -/

/-- **Upper numbering on $\mathrm{Gal}(\Omega/K)$** (Milne, *CFT*, I, §4, p. 46, definition in prose, using
Proposition 4.4): $\sigma \in G^v$ if and only if $\sigma|_L \in \mathrm{Gal}(L/K)^v$ for every finite Galois
$L/K$ inside $\Omega$. -/
@[kb "milne2020cft" "Ch. I, §4, p. 46 (upper numbering on Gal(Ω/K))"]
def upperRamificationGroupInf (v : ℝ) : Subgroup (Ω ≃ₐ[K] Ω) :=
  ⨅ (L : IntermediateField K Ω) (h : FiniteDimensional K L ∧ IsGalois K L),
    haveI := h.1; haveI := h.2; (upperRamificationGroup L v).comap (AlgEquiv.restrictNormalHom L)

end NumberFieldKB.MilneCFT.LocalCFT
