import NumberFieldKB.MilneCFT.Ch8.CubicTauCeti
import NumberFieldKB.MilneCFT.Ch8.Reciprocity
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.WeilBNT.IdeleCharacterExtension
import NumberFieldKB.HeckeCharacter.Local
import NumberFieldKB.MilneCFT.Ch8.Example101Aux
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Milne, *Class Field Theory*, Example VIII.10.1: a Hecke character of $\mathbb Q(\zeta_3)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §10, printed
p. 262 (pdf p. 271). $K = \mathbb Q(\rho)$, $\rho$ a primitive cube root of $1$, $D \in \mathbb Z$ cube-free. For
$p \equiv 2 \pmod 3$ the prime $p$ stays prime in $K$; for $p \equiv 1 \pmod 3$, $p = \pi\bar\pi$ with $\pi \equiv 1
\pmod 3$. There is a Hecke character $\chi$ (a continuous unitary character of the idèle class group) with
$\chi(p) = -1$ for the odd $p \not\equiv 1 \pmod 3$ and $\chi(\mathfrak p) = (D/\pi)_3\,\bar\pi/\sqrt p$ for
$\mathfrak p = (\pi)$, $\pi \equiv 1 \pmod 3$ (outside the primes dividing $3D$, where the values are not specified).

**Reading of the text.** The machine-read copy of p. 262 used here loses minus signs and Greek letters; the formula
above is the reading consistent with the rest of the page: Milne's remark after the theorem of Gauss
($L(s, E) = L(s - 1/2, \chi)$ for $E : X^3 + Y^3 + Z^3 = 0$ and $D = 1$) forces $\chi(p) = -1$ at the inert primes
(the local factor of $L(s,E)$ there is $(1 + p^{1-2s})^{-1}$), and a Hecke character equal to $+1$ on the inert primes
and to the same values on the split primes would differ from $\chi$ by a character that is $-1$ on the inert and $1$
on the split primes, which does not exist (its $L$-series would have a pole at $s=1$). Replacing $\bar\pi$ by $\pi$,
or $(D/\pi)_3$ by its inverse, gives the complex conjugate character with $D$ replaced by $D^2$ up to cubes, so the
statement for all cube-free $D$ covers these variants.

**Statement.** The values are read through a complex embedding $\sigma$ of $K$ (any of the two); $(D/\pi)_3$ is the
cubic residue symbol `CubicTC.cubSym`, $\bar\pi$ is `CubicTC.conj π`, and $\chi(\mathfrak p)$ is the value
$\chi_v(\varpi_v)$ of the local component at a uniformizer (the convention of `exists_heckeChar`).

**Proof.** $\chi = \chi_0\,\chi_D$:
* $\chi_0$, of infinity type $z \mapsto \bar z/|z|$ and conductor dividing $3$, by Weil's Proposition VII.8.17
  (`WeilBNT.weil_VII_8_prop17`): on the ideals prime to $3$, $\varphi_0((\alpha)) = \sigma(\bar\alpha)/|\sigma(\alpha)|$
  for the generator $\alpha \equiv 1 \pmod 3$ (unique: the six units of $\mathbb Z[\rho]$ are distinct mod $3$; it
  exists since $\mathbb Z[\rho]$ is a principal ideal domain and the units fill $(\mathbb Z[\rho]/3)^\times$);
* $\chi_D = \kappa \circ \psi_{L/K}$ for the Kummer extension $L = K(D^{1/3})$, with $\psi_{L/K}$ the idèlic Artin map
  (`idelicArtinTauCeti`) and $\kappa(g) = g(D^{1/3})/D^{1/3} \in \mu_3$; at an unramified prime its value is the cubic
  residue symbol (`idelicArtinTauCeti_frobenius`, `item_5_3`).
-/

open NumberField IsDedekindDomain NumberFieldKB.HeckeCharacter

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace Ex101

variable {K : Type} [Field K] [NumberField K]

/-- A Hecke character from a continuous idèle character trivial on $K^\times$. -/
def heckeOfIdele (ω : IdeleGroup (𝓞 K) K →* ℂˣ) (hc : Continuous ω)
    (hK : ∀ a : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) : HeckeCharacter K :=
  ⟨QuotientGroup.lift _ ω (by
      rintro _ ⟨a, rfl⟩
      exact (MonoidHom.mem_ker).mpr (hK a)),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hc⟩

theorem heckeOfIdele_apply (ω : IdeleGroup (𝓞 K) K →* ℂˣ) (hc : Continuous ω)
    (hK : ∀ a : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) (x : IdeleGroup (𝓞 K) K) :
    heckeOfIdele ω hc hK (x : IdeleClassGroup (𝓞 K) K) = ω x := rfl

theorem finiteComponent_heckeOfIdele (ω : IdeleGroup (𝓞 K) K →* ℂˣ) (hc : Continuous ω)
    (hK : ∀ a : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    (heckeOfIdele ω hc hK).finiteComponent v u = ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) := rfl

end Ex101

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- **Example 10.1** (Milne, *CFT*, VIII, Example 10.1, p. 262). Let $D \in \mathbb Z$ be cube-free and $\sigma$ a
complex embedding of $K = \mathbb Q(\zeta_3)$. There is a unitary Hecke character $\chi$ of $K$ such that
$\chi(p) = -1$ for every odd prime $p \equiv 2 \pmod 3$ not dividing $D$ ($p$ stays prime in $K$), and
$\chi(\mathfrak p) = (D/\pi)_3\,\bar\pi/\sqrt p$ for every prime $\mathfrak p = (\pi)$ of $K$ with $\pi \equiv 1
\pmod 3$ of norm $p \equiv 1 \pmod 3$, $p \nmid D$ (values through $\sigma$; $\chi$ is unramified at these primes). -/
@[kb "milne2020cft" "Ch. VIII, Example 10.1, p. 262"]
theorem example10_1 (D : ℤ) (hD : D ≠ 0) (_hcube : ∀ q : ℤ, q ^ 3 ∣ D → IsUnit q) (σ : K →+* ℂ) :
    ∃ χ : HeckeCharacter K, χ.IsUnitary ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 → ¬ (p : ℤ) ∣ D → ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal = Ideal.span {(p : 𝓞 K)} →
          χ.IsUnramifiedAt v ∧ (χ.finiteComponent v (QuadFormsKB.Analysis.ϖU v) : ℂ) = -1) ∧
      (∀ p : ℕ, p.Prime → p % 3 = 1 → ¬ (p : ℤ) ∣ D → ∀ π : 𝓞 K, Algebra.norm ℤ π = p → (3 : 𝓞 K) ∣ π - 1 →
        ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal = Ideal.span {π} →
          χ.IsUnramifiedAt v ∧ (χ.finiteComponent v (QuadFormsKB.Analysis.ϖU v) : ℂ) =
            σ ((CubicTC.cubSym (D : 𝓞 K) π : 𝓞 K) : K) * σ ((CubicTC.conj π : 𝓞 K) : K) / (Real.sqrt p : ℂ)) := by
  obtain ⟨ω0, hc0, hK0, hn0, hu0, hv0⟩ := Ex101.exists_omega0_values σ
  obtain ⟨ωD, hcD, hKD, hnD, huD, hvD⟩ := Ex101.exists_omegaD D hD σ
  have hc : Continuous (ω0 * ωD) := by
    have := hc0.mul hcD
    exact this
  have hK : ∀ a : Kˣ, (ω0 * ωD) (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
    intro a; rw [MonoidHom.mul_apply, hK0, hKD, mul_one]
  set χ : HeckeCharacter K := Ex101.heckeOfIdele (ω0 * ωD) hc hK with hχ
  have hfc : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      (χ.finiteComponent v u : ℂ) =
        (ω0 (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : ℂ) *
          (ωD (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : ℂ) := fun v u => rfl
  have hϖ : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((QuadFormsKB.Analysis.ϖU v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        WithZero.exp (-1) := fun v => by
    simpa using NumberFieldKB.LocalZeta.valued_ϖU_zpow v 1
  have unram : ∀ v : HeightOneSpectrum (𝓞 K), (3 : 𝓞 K) ∉ v.asIdeal → v ∉ Sset 3 {(D : K)} →
      χ.IsUnramifiedAt v := by
    intro v h3 hvS u hu
    apply Units.ext
    rw [hfc, hu0 v h3 u hu, huD v hvS u hu]
    simp
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    show ‖(((ω0 * ωD) x : ℂˣ) : ℂ)‖ = 1
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hn0, hnD, mul_one]
  · intro p hp hp2 hp3 hpD v hv
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
    have hξ3 : (3 : 𝓞 K) ∣ (-(p : 𝓞 K)) - 1 := by
      have : (p : 𝓞 K) = 3 * k + 2 := by exact_mod_cast hk
      exact ⟨-(k + 1), by rw [this]; ring⟩
    have hspan : v.asIdeal = Ideal.span {-(p : 𝓞 K)} := by rw [Ideal.span_singleton_neg]; exact hv
    have h3 : ((3 : ℕ) : 𝓞 K) ∉ v.asIdeal := Ex101.three_notMem_of_gen hspan hξ3
    have h3' : (3 : 𝓞 K) ∉ v.asIdeal := by simpa using h3
    have hDp : ¬ (p : 𝓞 K) ∣ (D : 𝓞 K) := by
      intro h
      have h1 := map_dvd (Algebra.norm ℤ) h
      have e : (p : 𝓞 K) = (((p : ℤ)) : 𝓞 K) := by simp
      rw [e, Ex101.norm_intCast, Ex101.norm_intCast] at h1
      exact hpD ((Int.pow_dvd_pow_iff (by norm_num)).1 h1)
    have hvS : v ∉ Sset 3 {(D : K)} := Ex101.notMem_Sset_of_gen hv h3 hDp
    refine ⟨unram v h3' hvS, ?_⟩
    rw [hfc, hv0 (-(p : 𝓞 K)) hξ3 v hspan _ (hϖ v), hvD v hvS _ (hϖ v),
      Ex101.powerResidue_inert hp hp3 hpD hv hvS]
    have hσ : σ (((-(p : 𝓞 K) : 𝓞 K)) : K) = -(p : ℂ) := by
      push_cast; simp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hσ]
    simp [hp0]
  · intro p hp hp1 hpD π hπN hπ3 v hv
    have hprime : Prime π := Ex101.prime_of_span hv
    have h3 := Ex101.three_notMem_of_gen hv hπ3
    have h3' : (3 : 𝓞 K) ∉ v.asIdeal := by simpa using h3
    have hDπ := Ex101.not_dvd_of_norm hp hπN hpD
    have hvS := Ex101.notMem_Sset_of_gen hv h3 hDπ
    refine ⟨unram v h3' hvS, ?_⟩
    rw [hfc, hv0 π hπ3 v hv _ (hϖ v), hvD v hvS _ (hϖ v)]
    have hvπ : v = CubicTC.specOf hprime := HeightOneSpectrum.ext hv
    have hpr : powerResidue 3 (D : K) v = ((CubicTC.cubSym (D : 𝓞 K) π : 𝓞 K) : K) := by
      rw [hvπ]
      have := CubicTC.powerResidue_prime hprime (Ex101.not_dvd_three hprime hπ3) hDπ
      simpa using this
    rw [hpr, Ex101.norm_sigma_of_norm σ hπN, ← Ex101.sigma_conj]
    ring

end NumberFieldKB.MilneCFT.Ch8
