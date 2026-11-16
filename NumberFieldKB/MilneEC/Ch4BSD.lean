import NumberFieldKB.MilneEC.Ch4bStatements
import NumberFieldKB.MilneEC.Ch4NeronTate
import NumberFieldKB.MilneEC.Ch4bRegulator
import NumberFieldKB.MilneEC.Ch4VarietyZeta
import NumberFieldKB.FormalConjectures.EllipticCurve
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Milne, *Elliptic Curves*, Chapter IV §10: the conjectures, and comparisons with Formal Conjectures

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, §10 ("The conjecture of Birch and
Swinnerton-Dyer"), pdf pp. 169–175 (printed page = pdf page − 8).

Milne's conjectures are stated here as `Prop`-valued **definitions**. None of them is assumed anywhere.

* **Conjecture 10.1** (`Conjecture10_1`, pdf p. 169): $\prod_{p \le P,\ p\text{ good}} N_p/p \sim C(\log P)^r$,
  $r = \operatorname{rank} E(\mathbb Q)$.
* **Conjecture 10.2** (`Conjecture10_2`, Hasse–Weil, pdf p. 170): the zeta function $\zeta(V, s)$ of a nonsingular
  projective variety over $\mathbb Q$ continues to a meromorphic function on $\mathbb C$. Only the continuation is
  stated: Milne asks for "a functional equation relating $\zeta(V, s)$ with $\zeta(V, d + 1 - s)$" without saying
  which, and any nonzero meromorphic function satisfies *some* such relation. Varieties are complete intersections,
  as in `Ch4VarietyZeta.lean`.
* **Conjecture 10.3** (`Conjecture10_3`, pdf p. 172): $\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$ continues
  meromorphically to $\mathbb C$ and $\Lambda(E, s) = w_E\Lambda(E, 2 - s)$, $w_E = \pm 1$.
* **Conjecture 10.5** (`Conjecture10_5`, Birch and Swinnerton-Dyer, pdf p. 173): for $P_1, \dots, P_r$ linearly
  independent in $E(\mathbb Q)$,
  $L(E, s) \sim \Omega\prod_{p\text{ bad}} c_p\,[Ш]\det\langle P_i, P_j\rangle/(E(\mathbb Q) : \sum\mathbb ZP_i)^2
  \cdot(s - 1)^r$ as $s \to 1$, for a minimal equation of $E$.
* Conjecture 5.3 (Sha finite) is `Conjecture5_3` in `Ch4Rank.lean`.

## Comparisons with Formal Conjectures (vendored in `NumberFieldKB.FormalConjectures.EllipticCurve`)

* `completedLHasMeromorphicContinuation_iff`: the continuation half of Conjecture 10.3 for $E$ holds iff
  Formal Conjectures' `HasMeromorphicContinuation E L` holds for some `L`. Hence `Conjecture10_3` implies the
  meromorphic Hasse–Weil statement over $\mathbb Q$ (`conjecture10_3_existsMeromorphicContinuationRat`), and so does
  Formal Conjectures' analytic one (`existsAnalyticContinuationRat_completedL`). Conjecture 10.3 and "an analytic
  continuation of $L(E, s)$ exists" are **not** logically equivalent: 10.3 has a functional equation and allows poles.
* **Normalization of the height pairing.** Milne's pairing is $\langle P, Q\rangle = \hat h(P + Q) - \hat h(P) -
  \hat h(Q)$ with $\hat h = \lim h_x(2^nP)/4^n$ (§§4, 6). Formal Conjectures (like Silverman and the LMFDB) uses half
  of it in the regulator. So the determinant in Conjecture 10.5 as printed is $2^r$ times the standard regulator
  (Milne's own footnote on pdf p. 129 warns that normalizations differ by a factor 2).
  `regulatorQuotient_eq_two_pow_mul_regulator` proves the identity
  $\det\langle P_i, P_j\rangle/(E(\mathbb Q):\sum\mathbb ZP_i)^2 = 2^r\operatorname{Reg}/[E(\mathbb Q)_{\mathrm{tors}}]^2$.
  `Conjecture10_5Corrected` divides Milne's constant by $2^r$.
* `conjecture10_5Corrected_iff_strongBSD`: for a minimal equation, the corrected Conjecture 10.5 is equivalent to
  Formal Conjectures' `StrongBSD` over $\mathbb Q$, given three named comparison statements whose proofs are not
  formalized: the two Tate–Shafarevich groups are isomorphic (`ShaComparison`), Milne's $\Omega$ is the global period
  for a minimal equation (`PeriodComparison`), and $\prod_{p\text{ bad}} c_p$ over $\mathbb Q_p$ is Formal
  Conjectures' Tamagawa product over the adic completions (`TamagawaComparison`).
* `conjecture10_5_iff_corrected_of_rank_eq_zero`: in rank $0$ the printed and corrected forms agree, so
  `conjecture10_5_iff_strongBSD_of_rank_eq_zero`. `not_conjecture10_5_and_corrected`: in positive rank they
  contradict each other, so `not_conjecture10_5_of_strongBSD`: `StrongBSD` refutes the printed form.
* Finite generation of $E(\mathbb Q)$ (Mordell's theorem, Theorem I.2.1, here a named statement) is an instance
  argument `[Module.Finite ℤ E.toAffine.Point]` throughout, as in the vendored `StrongBSD`.
-/

open WeierstrassCurve Filter Topology

namespace NumberFieldKB.MilneEC

/-! ## Conjecture 10.1 -/

open scoped Classical in
/-- $f(P) = \prod_{p \le P,\ p \text{ good}} N_p/p$ (Milne pdf p. 169). -/
noncomputable def bsdPartialProduct (E : WeierstrassCurve ℚ) (x : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (x + 1)).filter (IsGoodPrime E), numPointsAt E p / p

/-- **Conjecture 10.1** (Milne, *EC*, IV, Conjecture 10.1, pdf p. 169; not assumed anywhere): for each elliptic curve
$E$ over $\mathbb Q$ there is a constant $C$ with $f(P) \sim C(\log P)^r$, $r = \operatorname{rank} E(\mathbb Q)$
(Milne's "$\lim f(P) = C\log(P)^r$", restated by him as $f(P) \sim C\log(P)^r$: the ratio tends to $1$; $C > 0$
since $f > 0$). -/
@[kb "milne2006ec" "Ch. IV, Conjecture 10.1, pdf p. 169"]
def Conjecture10_1 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ C : ℝ, 0 < C ∧
    Tendsto (fun x : ℕ => bsdPartialProduct E x / (C * Real.log x ^ rank E)) atTop (𝓝 1)

/-! ## Conjecture 10.2 -/

/-- **Conjecture 10.2, Hasse–Weil** (Milne, *EC*, IV, Conjecture 10.2, pdf p. 170; not assumed anywhere), the
continuation: for a nonsingular projective variety $V \subset \mathbb P^n$ over $\mathbb Q$, cut out as a complete
intersection by homogeneous $F_1, \dots, F_r$ (so $d = \dim V = n - r$), $\zeta(V, s)$ agrees on
$\Re s > d + 1$ (where Milne says the product converges) with a meromorphic function on $\mathbb C$. The functional
equation "relating $\zeta(V, s)$ with $\zeta(V, d+1-s)$" is not specified in the source and is not stated. -/
@[kb "milne2006ec" "Ch. IV, Conjecture 10.2 (Hasse-Weil), pdf p. 170"]
def Conjecture10_2 : Prop :=
  ∀ (n r : ℕ) (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ), (∀ i, ∃ m, (F i).IsHomogeneous m) →
    VarietyZeta.IsNonsingularCI F →
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      ∀ s : ℂ, (n : ℝ) - r + 1 < s.re → Z s = VarietyZeta.varietyZeta F s

/-! ## Conjecture 10.3 -/

/-- **Conjecture 10.3** (Milne, *EC*, IV, Conjecture 10.3, pdf p. 172; not assumed anywhere): for every elliptic
curve $E$ over $\mathbb Q$, $\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$ continues to a meromorphic function on
$\mathbb C$ with $\Lambda(E, s) = w_E\Lambda(E, 2 - s)$, $w_E = \pm 1$ (`IsSignOfFunctionalEquation`). The conductor
$N$ is existentially quantified among the $N$ satisfying Milne's description (`Vb.IsConductorOf`), since Ogg's formula
fixing the exponents at $2$ and $3$ is not formalized. -/
@[kb "milne2006ec" "Ch. IV, Conjecture 10.3, pdf p. 172"]
def Conjecture10_3 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ (N : ℕ) (w : ℤ), IsSignOfFunctionalEquation E N w

/-- The continuation half of Conjecture 10.3 for $E$ and $N$: $N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$, on
$\Re s > 3/2$, extends to a meromorphic function on $\mathbb C$. -/
def CompletedLHasMeromorphicContinuation (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  ∃ Λ : ℂ → ℂ, MeromorphicOn Λ Set.univ ∧ ∀ s : ℂ, 3 / 2 < s.re →
    Λ s = (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * E.LSeries s

/-! ## Conjecture 10.5 -/

/-- $E$ is given by a **minimal equation** over $\mathbb Q$ (Milne's "minimum equation", pdf p. 173): the equation is
minimal over $\mathbb Z_p$ for every prime $p$ (in particular it has integral coefficients). -/
def IsMinimalOverRat (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], (E.baseChange ℚ_[p]).IsMinimal ℤ_[p]

/-- Milne's $\Omega = \int_{E(\mathbb R)}|\omega|$, $\omega = dx/(2y + a_1x + a_3)$ for the given equation
(pdf p. 173), computed as Formal Conjectures' `realPeriod`: $2\int_{\mathbb R} dx/\sqrt{4x^3 + b_2x^2 + 2b_4x + b_6}$
(integrand $0$ where the cubic is not positive). -/
noncomputable def realPeriodOf (E : WeierstrassCurve ℚ) : ℝ :=
  FormalConjectures.realPeriod (E.map (algebraMap ℚ ℝ))

/-- Milne's $c_p = (E(\mathbb Q_p) : E^0(\mathbb Q_p))$ (pdf p. 173), $E^0(\mathbb Q_p)$ the points with nonsingular
reduction on a minimal model over $\mathbb Z_p$, computed as Formal Conjectures' local `tamagawaNumber`. -/
noncomputable def tamagawaNumberAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℕ :=
  FormalConjectures.tamagawaNumber ℚ_[p]
    ((E.toProjective⁄ℚ_[p]).minimal ℤ_[p] |>.integralModel ℤ_[p])

open scoped Classical in
/-- $\prod_{p \text{ bad}} c_p$ (pdf p. 173). -/
noncomputable def tamagawaProductBad (E : WeierstrassCurve ℚ) : ℕ :=
  ∏ᶠ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    if IsGoodPrime E p then 1 else tamagawaNumberAt E p

section Pairing

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Milne's Néron–Tate pairing $\langle P, Q\rangle = \hat h(P + Q) - \hat h(P) - \hat h(Q)$ on $E(\mathbb Q)$
(`neronTatePairing`, §6) as a $\mathbb Z$-bilinear map. -/
noncomputable def neronTateBilin : E.toAffine.Point →ₗ[ℤ] E.toAffine.Point →ₗ[ℤ] ℝ :=
  ((isQuadraticForm_iff_exists_quadraticMap (by rw [ringChar.eq ℝ 0]; norm_num)
    (canonicalHeight E.toAffine)).1 (prop_4_9 E.toAffine)).choose.polarBilin

theorem neronTateBilin_apply (P Q : E.toAffine.Point) :
    neronTateBilin E P Q = neronTatePairing E.toAffine P Q := by
  have hQ := ((isQuadraticForm_iff_exists_quadraticMap (by rw [ringChar.eq ℝ 0]; norm_num)
    (canonicalHeight E.toAffine)).1 (prop_4_9 E.toAffine)).choose_spec
  simp only [neronTateBilin, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, neronTatePairing,
    polarPairingFun]
  simp only [hQ]

variable [Module.Finite ℤ E.toAffine.Point]

/-- Milne's leading constant in Conjecture 10.5 (pdf p. 173):
$\Omega\prod_{p\text{ bad}}c_p\,[Ш(E/\mathbb Q)]\det(\langle P_i, P_j\rangle)/(E(\mathbb Q) : \sum\mathbb ZP_i)^2$. -/
noncomputable def milneBSDConstant {r : ℕ} (P : Fin r → E.toAffine.Point) : ℝ :=
  realPeriodOf E * tamagawaProductBad E * Nat.card (tateShafarevich ℚ E) *
    regulatorQuotient (neronTateBilin E) P

/-- **Conjecture 10.5, Birch and Swinnerton-Dyer, as printed** (Milne, *EC*, IV, Conjecture 10.5, pdf p. 173; not
assumed anywhere), applied to the equation $E$ (Milne takes it minimal: see `Conjecture10_5All`, and
`IsMinimalOverRat` in the comparisons): $Ш(E/\mathbb Q)$ is finite (so that $[Ш]$ makes sense) and,
for all linearly independent $P_1, \dots, P_r \in E(\mathbb Q)$, $r = \operatorname{rank}$, the $L$-series continues
meromorphically (Conjecture 10.3) to a function $L$ with $L(s) \sim C\,(s - 1)^r$ as $s \to 1$, $C$ =
`milneBSDConstant E P` (the ratio tends to $1$; this forces $C \ne 0$). -/
@[kb "milne2006ec" "Ch. IV, Conjecture 10.5 (Birch and Swinnerton-Dyer), pdf p. 173"]
def Conjecture10_5 : Prop :=
  ∀ P : Fin (rank E) → E.toAffine.Point, LinearIndependent ℤ P →
    Finite (tateShafarevich ℚ E) ∧ ∃ L : ℂ → ℂ, FormalConjectures.HasMeromorphicContinuation E L ∧
      Tendsto (fun s => L s / ((milneBSDConstant E P : ℂ) * (s - 1) ^ rank E)) (𝓝[≠] 1) (𝓝 1)

/-- **Conjecture 10.5 with the standard normalization of the height pairing**: as `Conjecture10_5`, with the
pairing $\frac12(\hat h(P+Q) - \hat h(P) - \hat h(Q))$, i.e. Milne's constant divided by $2^r$. -/
def Conjecture10_5Corrected : Prop :=
  ∀ P : Fin (rank E) → E.toAffine.Point, LinearIndependent ℤ P →
    Finite (tateShafarevich ℚ E) ∧ ∃ L : ℂ → ℂ, FormalConjectures.HasMeromorphicContinuation E L ∧
      Tendsto (fun s => L s / ((milneBSDConstant E P / 2 ^ rank E : ℝ) * (s - 1) ^ rank E)) (𝓝[≠] 1) (𝓝 1)

end Pairing

/-- **Conjecture 10.5 for all elliptic curves over $\mathbb Q$** (Milne, *EC*, IV, Conjecture 10.5, pdf p. 173; not
assumed anywhere): `Conjecture10_5 E` for every $E$ given by a minimal equation, with $E(\mathbb Q)$ finitely
generated (Mordell's theorem, an instance argument here). -/
@[kb "milne2006ec" "Ch. IV, Conjecture 10.5 (Birch and Swinnerton-Dyer), pdf p. 173"]
def Conjecture10_5All : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] [Module.Finite ℤ E.toAffine.Point], IsMinimalOverRat E →
    Conjecture10_5 E

/-! ## The named comparison statements -/

/-- **Comparison of the Tate–Shafarevich groups** (named statement; not proved here): for an elliptic curve over
$\mathbb Q$, the group `tateShafarevich ℚ E` of `Ch4Selmer.lean` (classes in $H^1$ of the abstract Galois group,
continuous for the Krull topology, locally trivial) is isomorphic to Formal Conjectures' (continuous cohomology of
the discrete module $E(\bar{\mathbb Q})$, locally trivial). Both are the classical $Ш(E/\mathbb Q)$; the comparison
of the two cochain models of continuous $H^1$ is not formalized. -/
structure ShaComparison : Prop where
  equiv : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    Nonempty (tateShafarevich ℚ E ≃+ FormalConjectures.tateShafarevich E.toAffine)

/-- **Comparison of the periods** (named statement; not proved here): for a minimal equation over $\mathbb Q$,
Milne's $\Omega = \int_{E(\mathbb R)}|\omega|$ is Formal Conjectures' global period (whose discriminant correction
factor $(|\Delta|/N(\mathfrak D_{E}))^{1/12}$ is then $1$). -/
structure PeriodComparison : Prop where
  eq : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsMinimalOverRat E →
    realPeriodOf E = FormalConjectures.period E

/-- **Comparison of the Tamagawa products** (named statement; not proved here): Milne's $\prod_{p\text{ bad}} c_p$,
computed over $\mathbb Q_p$, is Formal Conjectures' product over all nonzero primes of $\mathbb Z$ of the local
Tamagawa numbers over the adic completions of $\mathbb Q$ (this needs $c_p = 1$ at good primes and
$\mathbb Q_p \cong \mathbb Q_{(p)}^\wedge$). -/
structure TamagawaComparison : Prop where
  eq : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (tamagawaProductBad E : ℝ) = FormalConjectures.tamagawaProduct E.toProjective

/-! ## Asymptotics at $s = 1$ and the leading coefficient -/

/-- $L(s) \sim C(s - 1)^r$ as $s \to 1$ (ratio tending to $1$) iff $C \ne 0$, $L$ has order $r$ at $1$ and
trailing coefficient $C$. -/
theorem tendsto_div_mul_pow_iff {L : ℂ → ℂ} (hL : MeromorphicAt L 1) (C : ℂ) (r : ℕ) :
    Tendsto (fun s => L s / (C * (s - 1) ^ r)) (𝓝[≠] 1) (𝓝 1) ↔
      C ≠ 0 ∧ meromorphicOrderAt L 1 = r ∧ meromorphicTrailingCoeffAt L 1 = C := by
  by_cases hC : C = 0
  · have hlim : Tendsto (fun s => L s / (C * (s - 1) ^ r)) (𝓝[≠] 1) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun s => by simp [hC])
    constructor
    · intro h; exact absurd (tendsto_nhds_unique h hlim) one_ne_zero
    · rintro ⟨h, -⟩; exact absurd hC h
  by_cases ht : meromorphicOrderAt L 1 = ⊤
  · have h0 : L =ᶠ[𝓝[≠] 1] 0 := meromorphicOrderAt_eq_top_iff.1 ht
    have hlim : Tendsto (fun s => L s / (C * (s - 1) ^ r)) (𝓝[≠] 1) (𝓝 0) :=
      tendsto_const_nhds.congr' (by filter_upwards [h0] with s hs; simp [hs])
    constructor
    · intro h; exact absurd (tendsto_nhds_unique h hlim) one_ne_zero
    · rintro ⟨-, h, -⟩; rw [ht] at h; exact absurd h (WithTop.top_ne_coe)
  obtain ⟨g, hg, hg0, hev⟩ := (meromorphicOrderAt_ne_top_iff hL).1 ht
  set n := (meromorphicOrderAt L 1).untop₀ with hn
  have hord : meromorphicOrderAt L 1 = (n : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hL).2 ⟨g, hg, hg0, hev⟩
  have hcoef : meromorphicTrailingCoeffAt L 1 = g 1 :=
    hg.meromorphicTrailingCoeffAt_of_eq_nhdsNE hev
  rw [hord, hcoef]
  have hrat : ∀ᶠ s in 𝓝[≠] (1 : ℂ), L s / (C * (s - 1) ^ r) = (s - 1) ^ (n - r) * g s / C := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
    have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    rw [hs, smul_eq_mul, zpow_sub₀ h1]
    simp only [zpow_natCast]
    field_simp
  have hgc : ContinuousAt g 1 := hg.continuousAt
  rw [tendsto_congr' hrat]
  rcases lt_trichotomy n r with hlt | heq | hgt
  · -- n < r
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (r : ℤ) - n = k + 1 := ⟨(r - n - 1).toNat, by omega⟩
    have hk' : n - r = -((k : ℤ) + 1) := by omega
    have hA : Tendsto (fun s : ℂ => (s - 1) ^ (n - r) * g s / C * (s - 1) ^ (k + 1)) (𝓝[≠] 1)
        (𝓝 (g 1 / C)) := by
      have : Tendsto (fun s : ℂ => g s / C) (𝓝[≠] 1) (𝓝 (g 1 / C)) :=
        (hgc.div_const C).tendsto.mono_left nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs1
      have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
      rw [hk', zpow_neg, zpow_add_one₀ h1]
      simp only [zpow_natCast]
      field_simp
      ring
    constructor
    · intro h
      have hB : Tendsto (fun s : ℂ => (s - 1) ^ (n - r) * g s / C * (s - 1) ^ (k + 1)) (𝓝[≠] 1)
          (𝓝 (1 * 0)) := by
        refine h.mul ?_
        have : Tendsto (fun s : ℂ => (s - 1) ^ (k + 1)) (𝓝 1) (𝓝 ((1 - 1 : ℂ) ^ (k + 1))) :=
          (((continuous_id.sub continuous_const).pow (k + 1)).tendsto 1)
        simpa using this.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
      have := tendsto_nhds_unique hA hB
      rw [mul_zero, div_eq_zero_iff] at this
      exact absurd (this.resolve_right hC) hg0
    · rintro ⟨-, h, -⟩
      exfalso
      have : (n : WithTop ℤ) = ((r : ℤ) : WithTop ℤ) := by simpa using h
      have := WithTop.coe_injective this
      omega
  · have h0 : n - r = 0 := by omega
    simp only [h0, zpow_zero, one_mul]
    have hT : Tendsto (fun s : ℂ => g s / C) (𝓝[≠] 1) (𝓝 (g 1 / C)) :=
      (hgc.div_const C).tendsto.mono_left nhdsWithin_le_nhds
    constructor
    · intro h
      have := tendsto_nhds_unique hT h
      exact ⟨hC, by rw [heq]; rfl, (div_eq_one_iff_eq hC).1 this⟩
    · rintro ⟨-, -, h⟩
      rw [h, div_self hC] at hT
      exact hT
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n - r = ((m + 1 : ℕ) : ℤ) := ⟨(n - r - 1).toNat, by omega⟩
    simp only [hm, zpow_natCast]
    have hT : Tendsto (fun s : ℂ => (s - 1) ^ (m + 1) * g s / C) (𝓝[≠] 1) (𝓝 0) := by
      have : Tendsto (fun s : ℂ => (s - 1) ^ (m + 1) * g s / C) (𝓝 1)
          (𝓝 ((1 - 1 : ℂ) ^ (m + 1) * g 1 / C)) :=
        ((((continuous_id.sub continuous_const).pow (m + 1)).continuousAt.mul hgc).div_const C).tendsto
      simpa using this.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    constructor
    · intro h; exact absurd (tendsto_nhds_unique h hT) one_ne_zero
    · rintro ⟨-, h, -⟩
      exfalso
      have : (n : WithTop ℤ) = ((r : ℤ) : WithTop ℤ) := by simpa using h
      have := WithTop.coe_injective this
      omega

/-! ## Conjecture 10.3 against Formal Conjectures -/

/-- $s \mapsto b^{s/2}$ is meromorphic for $b \ne 0$. -/
private lemma meromorphic_cpow_half (b : ℂ) (hb : b ≠ 0) : Meromorphic fun s : ℂ => b ^ (s / 2) := fun x =>
  ((Differentiable.const_cpow (by fun_prop) (Or.inl hb) : Differentiable ℂ fun s : ℂ => b ^ (s / 2)).analyticAt
    x).meromorphicAt

/-- $s \mapsto b^{-s}$ is meromorphic for $b \ne 0$. -/
private lemma meromorphic_cpow_neg (b : ℂ) (hb : b ≠ 0) : Meromorphic fun s : ℂ => b ^ (-s) := fun x =>
  ((Differentiable.const_cpow (by fun_prop) (Or.inl hb) : Differentiable ℂ fun s : ℂ => b ^ (-s)).analyticAt
    x).meromorphicAt

/-- $\Gamma$ is meromorphic on $\mathbb C$. -/
private lemma meromorphic_Gamma : Meromorphic Complex.Gamma := by
  intro x
  have h := ((Complex.differentiable_one_div_Gamma.analyticAt x).meromorphicAt).inv
  convert h using 1
  funext s
  simp

/-- The continuation half of Conjecture 10.3 for $E$ (any $N > 0$) is equivalent to Formal Conjectures'
meromorphic continuation of $L(E, s)$. -/
theorem completedLHasMeromorphicContinuation_iff (E : WeierstrassCurve ℚ) {N : ℕ} (hN : 0 < N) :
    CompletedLHasMeromorphicContinuation E N ↔ ∃ L, FormalConjectures.HasMeromorphicContinuation E L := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  have hA := meromorphic_cpow_half (N : ℂ) hN0
  have hB := meromorphic_cpow_neg (2 * Real.pi : ℂ) h2π
  have hG := meromorphic_Gamma
  constructor
  · rintro ⟨Λ, hΛ, h⟩
    refine ⟨fun s => Λ s * ((N : ℂ) ^ (s / 2))⁻¹ * ((2 * Real.pi : ℂ) ^ (-s))⁻¹ * (Complex.Gamma s)⁻¹,
      fun x => ?_, fun s hs => ?_⟩
    · exact ((((hΛ x (Set.mem_univ x)).mul (hA x).inv).mul (hB x).inv).mul (hG x).inv)
    · have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
      have h1 : (N : ℂ) ^ (s / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hN0]
      have h2 : (2 * Real.pi : ℂ) ^ (-s) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, h2π]
      beta_reduce
      rw [h s hs]
      field_simp
  · rintro ⟨L, hL, h⟩
    refine ⟨fun s => (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * L s,
      fun x _ => ?_, fun s hs => by beta_reduce; rw [h s hs]⟩
    exact (((hA x).mul (hB x)).mul (hG x)).mul (hL x)

/-- Conjecture 10.3 implies the meromorphic Hasse–Weil statement of Formal Conjectures over $\mathbb Q$. -/
theorem conjecture10_3_existsMeromorphicContinuationRat (h : Conjecture10_3) :
    FormalConjectures.ExistsMeromorphicContinuationRat := by
  intro E _
  obtain ⟨N, w, hN, -, Λ, hΛ, hΛE, -⟩ := h E
  exact (completedLHasMeromorphicContinuation_iff E hN.1).1 ⟨Λ, hΛ, hΛE⟩

/-- Formal Conjectures' analytic Hasse–Weil statement over $\mathbb Q$ (`exists_hasAnalyticContinuation_rat`)
implies the continuation half of Conjecture 10.3 for every $N > 0$. -/
theorem existsAnalyticContinuationRat_completedL (h : FormalConjectures.ExistsAnalyticContinuationRat)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : 0 < N) : CompletedLHasMeromorphicContinuation E N := by
  obtain ⟨L, hL⟩ := h E
  exact (completedLHasMeromorphicContinuation_iff E hN).2 ⟨L, hL.hasMeromorphicContinuation⟩

/-! ## The regulator: Milne's normalization against Formal Conjectures' -/

section Lift

variable (M : Type*) [AddCommGroup M]

/-- Lifts of a basis of $M/M_{\mathrm{tors}}$ are linearly independent. -/
private lemma lift_linearIndependent {d : ℕ} (b : Module.Basis (Fin d) ℤ (M ⧸ Submodule.torsion ℤ M)) :
    LinearIndependent ℤ (Quotient.out ∘ b) := by
  apply LinearIndependent.of_comp (Submodule.torsion ℤ M).mkQ
  have : (Submodule.torsion ℤ M).mkQ ∘ (Quotient.out ∘ b) = b := by
    funext i
    simp [Function.comp]
  rw [this]
  exact b.linearIndependent

/-- Lifts of a basis of $M/M_{\mathrm{tors}}$ together with the torsion span $M$. -/
private lemma lift_span_sup_torsion {d : ℕ} (b : Module.Basis (Fin d) ℤ (M ⧸ Submodule.torsion ℤ M)) :
    Submodule.span ℤ (Set.range (Quotient.out ∘ b)) ⊔ Submodule.torsion ℤ M = ⊤ := by
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (Submodule.torsion ℤ M).mkQ ∘ (Quotient.out ∘ b) = b := by
    funext i
    simp [Function.comp]
  rw [this]
  exact b.span_eq

private lemma finrank_quot_torsion :
    Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) = Module.finrank ℤ M :=
  finrank_quotient_eq_of_le_torsion le_rfl

end Lift

section Regulator

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

omit [E.IsElliptic] in
/-- The two naive heights agree: both are $h_x$ (zero at infinity). -/
theorem fc_naiveHeight_eq (P : E.toAffine.Point) :
    FormalConjectures.naiveHeight P = P.naiveHeight := by
  rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight₁]
  cases P with
  | zero =>
    rw [FormalConjectures.naiveHeight, show (WeierstrassCurve.Affine.Point.zero : E.toAffine.Point) = 0 from rfl,
      WeierstrassCurve.Affine.Point.xRep_zero]
    simp
  | some h => simp [FormalConjectures.naiveHeight, WeierstrassCurve.Affine.Point.xRep_some]

omit [E.IsElliptic] in
/-- The two canonical heights agree: both are $\lim_n h_x(2^nP)/4^n$. -/
theorem fc_canonicalHeight_eq (P : E.toAffine.Point) :
    FormalConjectures.canonicalHeight P = canonicalHeight E.toAffine P := by
  simp only [FormalConjectures.canonicalHeight, canonicalHeight, fc_naiveHeight_eq]

omit [E.IsElliptic] in
/-- Formal Conjectures' pairing is half of Milne's. -/
theorem fc_neronTatePairing_eq (P Q : E.toAffine.Point) :
    FormalConjectures.neronTatePairing P Q = neronTatePairing E.toAffine P Q / 2 := by
  simp only [FormalConjectures.neronTatePairing, neronTatePairing, polarPairingFun, fc_canonicalHeight_eq]

variable [Module.Finite ℤ E.toAffine.Point]

omit [E.IsElliptic] in
/-- There are $r = \operatorname{rank} E(\mathbb Q)$ linearly independent points. -/
theorem exists_linearIndependent_rank : ∃ P : Fin (rank E) → E.toAffine.Point, LinearIndependent ℤ P := by
  have h : rank E = Module.finrank ℤ (E.toAffine.Point ⧸ Submodule.torsion ℤ E.toAffine.Point) :=
    (finrank_quot_torsion E.toAffine.Point).symm
  exact ⟨(Quotient.out ∘ Module.finBasis ℤ (E.toAffine.Point ⧸ Submodule.torsion ℤ E.toAffine.Point)) ∘
    finCongr h, (lift_linearIndependent _ _).comp _ (finCongr h).injective⟩

/-- **Milne's regulator quotient is $2^r$ times the standard one**: for $P_1, \dots, P_r$ linearly independent,
$\det\langle P_i, P_j\rangle/(E(\mathbb Q) : \sum\mathbb ZP_i)^2 = 2^r\operatorname{Reg}(E)/[E(\mathbb Q)_{\mathrm{tors}}]^2$
with $\operatorname{Reg}$ Formal Conjectures' `regulator` (Remark 10.6(b) and Theorem 6.1). -/
theorem regulatorQuotient_eq_two_pow_mul_regulator (P : Fin (rank E) → E.toAffine.Point)
    (hP : LinearIndependent ℤ P) :
    regulatorQuotient (neronTateBilin E) P =
      2 ^ rank E * FormalConjectures.regulator E.toAffine /
        (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 := by
  set T := Submodule.torsion ℤ E.toAffine.Point with hT
  set b := Module.finBasis ℤ (E.toAffine.Point ⧸ T) with hb
  have h : rank E = Module.finrank ℤ (E.toAffine.Point ⧸ T) := (finrank_quot_torsion E.toAffine.Point).symm
  set e : Fin (rank E) ≃ Fin (Module.finrank ℤ (E.toAffine.Point ⧸ T)) := finCongr h with he
  set Q : Fin (rank E) → E.toAffine.Point := (Quotient.out ∘ b) ∘ e with hQdef
  have hQ0 : LinearIndependent ℤ (Quotient.out ∘ b) := lift_linearIndependent E.toAffine.Point b
  have hQ : LinearIndependent ℤ Q := hQ0.comp e e.injective
  have hgen : Submodule.span ℤ (Set.range Q) ⊔ T = ⊤ := by
    have : Set.range Q = Set.range (Quotient.out ∘ b) := e.surjective.range_comp (Quotient.out ∘ b)
    rw [this]
    exact lift_span_sup_torsion E.toAffine.Point b
  obtain ⟨-, hq⟩ := remark_10_6_b_basis (neronTateBilin E) Q hQ hgen
  rw [remark_10_6_b_independent (neronTateBilin E)
    (show Module.finrank ℤ E.toAffine.Point = rank E from rfl) P Q hP hQ, hq]
  have hcard : Nat.card T = Nat.card (AddCommGroup.torsion E.toAffine.Point) :=
    congrArg (fun H : AddSubgroup E.toAffine.Point => Nat.card H) Submodule.torsion_int
  rw [hcard]
  congr 1
  set G0 : Matrix (Fin (Module.finrank ℤ (E.toAffine.Point ⧸ T))) (Fin (Module.finrank ℤ (E.toAffine.Point ⧸ T))) ℝ :=
    Matrix.of fun i j => neronTatePairing E.toAffine ((Quotient.out ∘ b) i) ((Quotient.out ∘ b) j) with hG0
  have hdet : (Matrix.of fun i j => neronTateBilin E (Q i) (Q j)).det = G0.det := by
    rw [← Matrix.det_submatrix_equiv_self e G0]
    congr 1
    ext i j
    simp [hG0, hQdef, neronTateBilin_apply]
  have hpos : 0 < G0.det := (thm_6_1 E.toAffine _ hQ0).det_pos
  have hreg : FormalConjectures.regulator E.toAffine = (1 / 2 : ℝ) ^ Module.finrank ℤ (E.toAffine.Point ⧸ T) * G0.det := by
    unfold FormalConjectures.regulator
    have : FormalConjectures.neronTateMatrix (Quotient.out ∘ b) = (1 / 2 : ℝ) • G0 := by
      ext i j
      simp [FormalConjectures.neronTateMatrix, fc_neronTatePairing_eq, hG0]
      ring
    rw [this, Matrix.det_smul, Fintype.card_fin]
    exact abs_of_pos (by positivity)
  rw [hdet, hreg]
  have hexp : (1 / 2 : ℝ) ^ Module.finrank ℤ (E.toAffine.Point ⧸ T) = (1 / 2) ^ rank E := by rw [h]
  rw [hexp]
  have : (2 : ℝ) ^ rank E * (1 / 2) ^ rank E = 1 := by
    rw [← mul_pow]; norm_num
  calc G0.det = (2 ^ rank E * (1 / 2) ^ rank E) * G0.det := by rw [this, one_mul]
    _ = _ := by ring

/-- Given the three named comparisons, Milne's constant divided by $2^r$ is Formal Conjectures' `bsdQuotient`. -/
theorem milneBSDConstant_div_two_pow (hSha : ShaComparison) (hΩ : PeriodComparison) (hc : TamagawaComparison)
    (hmin : IsMinimalOverRat E) (P : Fin (rank E) → E.toAffine.Point) (hP : LinearIndependent ℤ P) :
    milneBSDConstant E P / 2 ^ rank E = FormalConjectures.bsdQuotient E.toAffine := by
  obtain ⟨φ⟩ := hSha.equiv E
  have hcard : Nat.card (tateShafarevich ℚ E) = Nat.card (FormalConjectures.tateShafarevich E.toAffine) :=
    Nat.card_congr φ.toEquiv
  unfold milneBSDConstant FormalConjectures.bsdQuotient
  rw [hΩ.eq E hmin, hc.eq E, hcard, regulatorQuotient_eq_two_pow_mul_regulator E P hP]
  have hd : |((NumberField.discr ℚ : ℤ) : ℝ)| = 1 := by simp
  rw [hd]
  simp only [Real.sqrt_one, one_mul]
  have h2 : (2 : ℝ) ^ rank E ≠ 0 := by positivity
  field_simp

end Regulator

/-! ## Conjecture 10.5 against `StrongBSD` -/

section BSD

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [Module.Finite ℤ E.toAffine.Point]

/-- **Conjecture 10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$**, for a minimal
equation, given the named comparisons of the Tate–Shafarevich groups, periods and Tamagawa products. -/
theorem conjecture10_5Corrected_iff_strongBSD (hSha : ShaComparison) (hΩ : PeriodComparison)
    (hc : TamagawaComparison) (hmin : IsMinimalOverRat E) :
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine := by
  obtain ⟨φ⟩ := hSha.equiv E
  constructor
  · intro h
    obtain ⟨P, hP⟩ := exists_linearIndependent_rank E
    obtain ⟨hfin, L, hL, ht⟩ := h P hP
    have hconst := milneBSDConstant_div_two_pow E hSha hΩ hc hmin P hP
    rw [hconst] at ht
    obtain ⟨-, hord, hcoef⟩ := (tendsto_div_mul_pow_iff (hL.1 1) _ _).1 ht
    exact ⟨L, hL, hord, Finite.of_equiv _ φ.toEquiv, hcoef⟩
  · rintro ⟨L, hL, hord, hfin, hcoef⟩ P hP
    refine ⟨Finite.of_equiv _ φ.symm.toEquiv, L, hL, ?_⟩
    have hconst := milneBSDConstant_div_two_pow E hSha hΩ hc hmin P hP
    rw [hconst]
    have hne : meromorphicTrailingCoeffAt L 1 ≠ 0 :=
      (hL.1 1).meromorphicTrailingCoeffAt_ne_zero (by rw [hord]; exact WithTop.coe_ne_top)
    rw [tendsto_div_mul_pow_iff (hL.1 1)]
    refine ⟨?_, hord, hcoef⟩
    rw [← hcoef]
    exact hne

/-- In rank $0$ the printed and corrected forms of Conjecture 10.5 are the same statement. -/
theorem conjecture10_5_iff_corrected_of_rank_eq_zero (h0 : rank E = 0) :
    Conjecture10_5 E ↔ Conjecture10_5Corrected E := by
  have key : ∀ P : Fin (rank E) → E.toAffine.Point,
      (milneBSDConstant E P / 2 ^ rank E : ℝ) = milneBSDConstant E P := fun P => by
    have h2 : (2 : ℝ) ^ rank E = 1 := by rw [h0, pow_zero]
    rw [h2, div_one]
  constructor
  · intro h P hP
    have := h P hP
    rwa [← key P] at this
  · intro h P hP
    have := h P hP
    rwa [key P] at this

/-- In positive rank the printed and corrected forms of Conjecture 10.5 contradict each other (they predict leading
coefficients differing by the factor $2^r \ne 1$). -/
theorem not_conjecture10_5_and_corrected (hr : 0 < rank E) (h₁ : Conjecture10_5 E)
    (h₂ : Conjecture10_5Corrected E) : False := by
  obtain ⟨P, hP⟩ := exists_linearIndependent_rank E
  obtain ⟨-, L₁, hL₁, t₁⟩ := h₁ P hP
  obtain ⟨-, L₂, hL₂, t₂⟩ := h₂ P hP
  obtain ⟨hC₁, -, hc₁⟩ := (tendsto_div_mul_pow_iff (hL₁.1 1) _ _).1 t₁
  obtain ⟨-, -, hc₂⟩ := (tendsto_div_mul_pow_iff (hL₂.1 1) _ _).1 t₂
  have hcongr : meromorphicTrailingCoeffAt L₁ 1 = meromorphicTrailingCoeffAt L₂ 1 :=
    meromorphicTrailingCoeffAt_congr_nhdsNE (hL₁.unique hL₂ 1)
  rw [hc₁, hc₂] at hcongr
  have hreal : milneBSDConstant E P = milneBSDConstant E P / 2 ^ rank E := by exact_mod_cast hcongr
  have hM : milneBSDConstant E P ≠ 0 := by exact_mod_cast hC₁
  have h2 : (2 : ℝ) ^ rank E = 1 := by
    field_simp at hreal
    exact hreal
  have : (1 : ℝ) < 2 ^ rank E := one_lt_pow₀ (by norm_num) hr.ne'
  linarith

/-- In rank $0$, Conjecture 10.5 as printed is Formal Conjectures' `StrongBSD` (given the named comparisons). -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero (hSha : ShaComparison) (hΩ : PeriodComparison)
    (hc : TamagawaComparison) (hmin : IsMinimalOverRat E) (h0 : rank E = 0) :
    Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine :=
  (conjecture10_5_iff_corrected_of_rank_eq_zero E h0).trans
    (conjecture10_5Corrected_iff_strongBSD E hSha hΩ hc hmin)

/-- **The erratum, formally**: in positive rank, Formal Conjectures' `StrongBSD` refutes Conjecture 10.5 as printed
(given the named comparisons). -/
theorem not_conjecture10_5_of_strongBSD (hSha : ShaComparison) (hΩ : PeriodComparison)
    (hc : TamagawaComparison) (hmin : IsMinimalOverRat E) (hr : 0 < rank E)
    (h : FormalConjectures.StrongBSD E.toAffine) : ¬ Conjecture10_5 E := fun h₁ =>
  not_conjecture10_5_and_corrected E hr h₁ ((conjecture10_5Corrected_iff_strongBSD E hSha hΩ hc hmin).2 h)

end BSD

end NumberFieldKB.MilneEC
