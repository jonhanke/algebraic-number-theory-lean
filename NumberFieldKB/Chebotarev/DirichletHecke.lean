import NumberFieldKB.NonVanishing.Hecke
import NumberFieldKB.Chebotarev.DirichletHeckeRat
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.NumberTheory.RamificationInertia.Inertia

/-!
# Dirichlet characters as Hecke characters of a number field
$K$ is a number field, $m\ge1$ and $\chi$ a Dirichlet character mod $m$ (`DirichletCharacter ℂ m`). The Hecke character
$\chi\circ N_{K/\mathbb Q}$ of $K$ is the composite $C_K\xrightarrow{N}C_{\mathbb Q}\xrightarrow{\tilde\chi}\mathbb C^\times$
of the idelic norm with the idelic character $\tilde\chi$ of $\mathbb Q$ attached to $\chi$.

**Convention.** We normalize so that the local component at a finite place $\mathfrak p$ with $N\mathfrak p$ prime to
$m$ is unramified and takes the value $\chi(N\mathfrak p)$ on a uniformizer (the *arithmetic* normalization: the Euler
factor of $L(s,\chi\circ N)$ at $\mathfrak p$ is $(1-\chi(N\mathfrak p)N\mathfrak p^{-s})^{-1}$, so over $\mathbb Q$ the
Hecke $L$-function is the Dirichlet $L$-function $L(s,\chi)$ with the Euler factors at $p\mid m$ possibly removed). With
the adelic character written as $\tilde\chi(x) = \chi(r(x))^{-1}$, $r : \mathbb A_{\mathbb Q}^\times\to(\mathbb Z/m)^\times$
the reduction of the $\hat{\mathbb Z}^\times$-component of $x/q$ ($q\in\mathbb Q^\times$ with
$x/q\in\mathbb R_{>0}\times\hat{\mathbb Z}^\times$), this is the inverse of the "naive" map: at $p\nmid m$ the idele $p$
(at the place $p$ only) has $r = p^{-1}\bmod m$. Same convention as Ramakrishnan–Valenza, *Fourier Analysis on Number
Fields*, §7.1 [unverified locator], and Neukirch, *Algebraic Number Theory*, Ch. VI, §6 (characters of the ray class
group, $\chi(\mathfrak p)$ on prime ideals) [unverified locator].

## Contents

* **`IsDirichletLift χ ψ`**: the Hecke character $\psi$ of $K$ has finite order dividing that of $\chi$, is unramified at
  every finite place $\mathfrak p$ with $N\mathfrak p$ prime to $m$, and $\psi_{\mathfrak p}(\varpi) = \chi(N\mathfrak p)$
  for every uniformizer $\varpi$ there. (These properties determine $\psi$, by weak approximation [not formalized].)
* Consequences for the Hecke $L$-function, all proved: the Euler factor
  $L_{\mathfrak p}(s,\psi) = (1-\chi(N\mathfrak p)N\mathfrak p^{-s})^{-1}$ (`IsDirichletLift.localL_eq`); $\psi$ is unitary
  and, if $\psi\ne1$, not a power of the norm (`IsDirichletLift.ne_normPow`); then **$L(s,\psi)$ is entire and
  $L(s,\psi)\ne0$ on $\operatorname{Re}s\ge1$**, in particular at $s = 1$ (`IsDirichletLift.heckeLCont_one`), and the Euler
  product at $s = 1$ converges in the natural order (`IsDirichletLift.hasProd_localL_one_normOrder`). $\psi\ne1$ as soon
  as $\chi(N\mathfrak p)\ne1$ for one $\mathfrak p$ with $N\mathfrak p$ prime to $m$ (`IsDirichletLift.ne_one_of_apply_ne_one`).
* **Composition with the norm** (`IsDirichletLift.comp_idelicNorm`, proved): if $\psi_0$ is attached to $\chi$ over
  $\mathbb Q$ and $N$ is an idelic norm $C_K\to C_{\mathbb Q}$ with its local description (the named input structure
  `IdelicNorm K`), then $\psi_0\circ N$ is attached to $\chi$ over $K$ ($\chi(p)^f = \chi(N\mathfrak p)$).
* **Existence**: over $\mathbb Q$, `RatIdele.ratDirichletChar` (`exists_isDirichletLift_rat`; it depends on the
  continuity stub `RatIdele.eventually_resMod_eq_one`); over $K$, `exists_isDirichletLift` also uses the named input
  `IdelicNormInput`.
-/

open IsDedekindDomain NumberField WithZero Filter
open QuadFormsKB NumberFieldKB.HeckeL NumberFieldKB.HeckeCharacter NumberFieldKB.NonVanishing

namespace NumberFieldKB.Chebotarev

noncomputable section

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

/-- **$\psi$ is the Hecke character $\chi\circ N_{K/\mathbb Q}$** attached to the Dirichlet character $\chi$ mod $m$:
$\psi^n = 1$ whenever $\chi^n = 1$; at every finite place $\mathfrak p$ of $K$ with $N\mathfrak p$ prime to $m$, $\psi$ is
unramified and $\psi_{\mathfrak p}(\varpi) = \chi(N\mathfrak p)$ for every uniformizer $\varpi$ of $K_{\mathfrak p}$. -/
@[kb "neukirch1999" "Ch. VI, §6 (Dirichlet characters as characters of the ray class group) [unverified locator]"]
structure IsDirichletLift (χ : DirichletCharacter ℂ m) (ψ : HeckeCharacter K) : Prop where
  pow_eq_one : ∀ n : ℕ, χ ^ n = 1 → ψ ^ n = 1
  isUnramifiedAt : ∀ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal).Coprime m → ψ.IsUnramifiedAt v
  finiteComponent_uniformizer : ∀ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal).Coprime m →
    ∀ ϖ : (v.adicCompletion K)ˣ, Valued.v (ϖ : v.adicCompletion K) = exp (-1) →
      (ψ.finiteComponent v ϖ : ℂ) = χ (Ideal.absNorm v.asIdeal)

namespace IsDirichletLift

variable {χ : DirichletCharacter ℂ m} {ψ : HeckeCharacter K}

/-- $\psi$ has finite order: $\psi^{\operatorname{ord}\chi} = 1$, $\operatorname{ord}\chi\ne0$. -/
theorem pow_orderOf_eq_one (h : IsDirichletLift χ ψ) : ψ ^ orderOf χ = 1 :=
  h.pow_eq_one _ (_root_.pow_orderOf_eq_one χ)

theorem orderOf_ne_zero (χ : DirichletCharacter ℂ m) : orderOf χ ≠ 0 :=
  (isOfFinOrder_of_finite χ).orderOf_pos.ne'

theorem isUnitary (h : IsDirichletLift χ ψ) : ψ.IsUnitary :=
  isUnitary_of_pow_eq_one (orderOf_ne_zero χ) h.pow_orderOf_eq_one

/-- **The Euler coefficient** at $\mathfrak p$ with $N\mathfrak p$ prime to $m$ is $\chi(N\mathfrak p)$. -/
theorem heckeCoeff_eq (h : IsDirichletLift χ ψ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (Ideal.absNorm v.asIdeal).Coprime m) : heckeCoeff ψ v = χ (Ideal.absNorm v.asIdeal) := by
  rw [heckeCoeff, if_pos (h.isUnramifiedAt v hv)]
  refine h.finiteComponent_uniformizer v hv _ ?_
  simpa using LocalZeta.valued_ϖU_zpow v 1

/-- **The Euler factor** of $L(s,\chi\circ N)$ at $\mathfrak p$ with $N\mathfrak p$ prime to $m$:
$(1-\chi(N\mathfrak p)N\mathfrak p^{-s})^{-1}$. -/
theorem localL_eq (h : IsDirichletLift χ ψ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (Ideal.absNorm v.asIdeal).Coprime m) (s : ℂ) :
    localL ψ s v = (1 - χ (Ideal.absNorm v.asIdeal) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  rw [localL, if_pos (h.isUnramifiedAt v hv), GlobalZeta.rV, Complex.ofReal_natCast]
  congr 3
  have := h.heckeCoeff_eq hv
  rwa [heckeCoeff, if_pos (h.isUnramifiedAt v hv)] at this


/-! ### The value on any element of $K_{\mathfrak p}^\times$ -/

/-- At $\mathfrak p$ with $N\mathfrak p$ prime to $m$: $\psi_{\mathfrak p}(u) = \chi(N\mathfrak p)^k$ when $v_{\mathfrak p}(u) = k\ge0$. -/
theorem finiteComponent_of_valued_eq (h : IsDirichletLift χ ψ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (Ideal.absNorm v.asIdeal).Coprime m) (k : ℕ) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = exp (-(k : ℤ))) :
    (ψ.finiteComponent v u : ℂ) = χ (Ideal.absNorm v.asIdeal) ^ k := by
  have hϖ : Valued.v ((Analysis.ϖU v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = exp (-1) := by
    simpa using LocalZeta.valued_ϖU_zpow v 1
  have hu' : Valued.v ((u * (Analysis.ϖU v ^ k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    have h2 := LocalZeta.valued_ϖU_zpow v (-(k : ℤ))
    rw [zpow_neg, zpow_natCast] at h2
    rw [Units.val_mul, map_mul, hu, h2, neg_neg, ← exp_add, neg_add_cancel, exp_zero]
  have hdec : u = (u * (Analysis.ϖU v ^ k)⁻¹) * Analysis.ϖU v ^ k := (inv_mul_cancel_right u _).symm
  rw [hdec, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, h.isUnramifiedAt v hv _ hu',
    h.finiteComponent_uniformizer v hv _ hϖ, Units.val_one, one_mul]

/-- If $\psi = \chi\circ N$ is nontrivial, it is not a power of the norm. -/
theorem ne_normPow (h : IsDirichletLift χ ψ) (hne : ψ ≠ 1) : ∀ c : ℂ, ψ ≠ normPow K c :=
  ne_normPow_of_pow_eq_one (orderOf_ne_zero χ) h.pow_orderOf_eq_one hne

/-- $\chi\circ N\ne1$ as soon as $\chi(N\mathfrak p)\ne1$ at one $\mathfrak p$ with $N\mathfrak p$ prime to $m$. -/
theorem ne_one_of_apply_ne_one (h : IsDirichletLift χ ψ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (Ideal.absNorm v.asIdeal).Coprime m) (hχ : χ (Ideal.absNorm v.asIdeal) ≠ 1) : ψ ≠ 1 := by
  rintro rfl
  apply hχ
  rw [← h.heckeCoeff_eq hv, heckeCoeff, if_pos (h.isUnramifiedAt v hv)]
  rfl

/-- **$L(s,\chi\circ N)$ is entire** when $\chi\circ N\ne1$. -/
theorem differentiable_heckeLCont (h : IsDirichletLift χ ψ) (hne : ψ ≠ 1) : Differentiable ℂ (heckeLCont ψ) :=
  HeckeL.differentiable_heckeLCont (h.ne_normPow hne)

/-- **$L(s,\chi\circ N)\ne0$ on $\operatorname{Re}s\ge1$** when $\chi\circ N\ne1$. -/
theorem heckeLCont_ne_zero (h : IsDirichletLift χ ψ) (hne : ψ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : heckeLCont ψ s ≠ 0 :=
  heckeLCont_ne_zero_of_one_le_re h.isUnitary (h.ne_normPow hne) hs

/-- **$L(s,\chi\circ N_{K/\mathbb Q})$ is holomorphic and nonzero at $s = 1$** when $\chi\circ N_{K/\mathbb Q}\ne1$. -/
@[kb "neukirch1999" "Ch. VII, §13 (non-vanishing of L(1, χ)) [unverified locator]"]
theorem heckeLCont_one (h : IsDirichletLift χ ψ) (hne : ψ ≠ 1) :
    DifferentiableAt ℂ (heckeLCont ψ) 1 ∧ heckeLCont ψ 1 ≠ 0 :=
  ⟨h.differentiable_heckeLCont hne 1, h.heckeLCont_ne_zero hne (by simp)⟩

/-- **The Euler product of $L(1,\chi\circ N)$ converges in the natural order** when $\chi\circ N\ne1$:
$\prod_{N\mathfrak p\le X}L_{\mathfrak p}(1,\chi\circ N)\to L(1,\chi\circ N)$. -/
theorem hasProd_localL_one_normOrder (h : IsDirichletLift χ ψ) (hne : ψ ≠ 1) :
    HasProd (localL ψ 1) (heckeLCont ψ 1) (QuadFormsKB.RegProd.normOrder K) :=
  NonVanishing.hasProd_localL_one_normOrder (orderOf_ne_zero χ) h.pow_orderOf_eq_one hne

end IsDirichletLift

/-! ### Composition with the idelic norm -/

/-- **The idelic norm** $N_{K/\mathbb Q} : C_K\to C_{\mathbb Q}$, as the data used here (a named input, not a
definition): a continuous homomorphism, a place $p = $ `place 𝔭` of $\mathbb Q$ under each finite place $\mathfrak p$ of
$K$, and the local description at $\mathfrak p$: $N\mathfrak p = p^{f}$, and $N(u)$ for $u\in K_{\mathfrak p}^\times$ (at
the place $\mathfrak p$, $1$ elsewhere) is an idele $y\in\mathbb Q_p^\times$ (at $p$, $1$ elsewhere) with
$v_p(y) = f\,v_{\mathfrak p}(u)$ ($y = N_{K_{\mathfrak p}/\mathbb Q_p}(u)$, $f = f(\mathfrak p\mid p)$).
Not in Mathlib v4.35.0. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on I_L and C_L) [unverified locator]"]
structure IdelicNorm (K : Type) [Field K] [NumberField K] where
  toHom : IdeleClassGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ
  place : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 ℚ)
  inertiaDeg : HeightOneSpectrum (𝓞 K) → ℕ
  absNorm_eq : ∀ v, Ideal.absNorm v.asIdeal = Ideal.absNorm (place v).asIdeal ^ inertiaDeg v
  map_ofAdicCompletion : ∀ v (u : (v.adicCompletion K)ˣ), ∃ y : ((place v).adicCompletion ℚ)ˣ,
    toHom (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ (place v) y ∧
    Valued.v (y : (place v).adicCompletion ℚ) = Valued.v (u : v.adicCompletion K) ^ inertiaDeg v

namespace IdelicNorm

variable (N : IdelicNorm K)

theorem inertiaDeg_ne_zero (v : HeightOneSpectrum (𝓞 K)) : N.inertiaDeg v ≠ 0 := by
  intro h0
  have h := N.absNorm_eq v
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h
  exact v.isPrime.ne_top h

theorem coprime_place {v : HeightOneSpectrum (𝓞 K)} (hv : (Ideal.absNorm v.asIdeal).Coprime m) :
    (Ideal.absNorm (N.place v).asIdeal).Coprime m := by
  rw [N.absNorm_eq v] at hv
  exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero (N.inertiaDeg_ne_zero v)) _ _).mp hv

end IdelicNorm

/-- **$\chi\circ N_{K/\mathbb Q}$**: if $\psi_0$ is the Hecke character of $\mathbb Q$ attached to $\chi$, then
$\psi_0\circ N_{K/\mathbb Q}$ is the Hecke character of $K$ attached to $\chi$: unramified at $\mathfrak p$ with
$N\mathfrak p$ prime to $m$, with value $\chi(p)^f = \chi(N\mathfrak p)$ on a uniformizer. -/
theorem IsDirichletLift.comp_idelicNorm {χ : DirichletCharacter ℂ m} {ψ₀ : HeckeCharacter ℚ}
    (h : IsDirichletLift χ ψ₀) (N : IdelicNorm K) : IsDirichletLift χ (ψ₀.comp N.toHom) := by
  have hfin : ∀ v (u : (v.adicCompletion K)ˣ) (y : ((N.place v).adicCompletion ℚ)ˣ),
      N.toHom (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
        IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ (N.place v) y →
      HeckeCharacter.finiteComponent (F := K) (ψ₀.comp N.toHom) v u = ψ₀.finiteComponent (N.place v) y := by
    intro v u y hy
    show ψ₀ (N.toHom (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u)) =
      ψ₀ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ (N.place v) y)
    rw [hy]
  refine ⟨fun n hn => ?_, fun v hv u hu => ?_, fun v hv ϖ hϖ => ?_⟩
  · refine ContinuousMonoidHom.ext fun c => ?_
    rw [pow_apply_aux]
    show (ψ₀ (N.toHom c)) ^ n = _
    rw [← pow_apply_aux, h.pow_eq_one n hn]
    rfl
  · obtain ⟨y, hy, hyv⟩ := N.map_ofAdicCompletion v u
    rw [hfin v u y hy]
    exact h.isUnramifiedAt _ (N.coprime_place hv) y (by rw [hyv, hu, one_pow])
  · obtain ⟨y, hy, hyv⟩ := N.map_ofAdicCompletion v ϖ
    rw [hfin v ϖ y hy, h.finiteComponent_of_valued_eq (N.coprime_place hv) (N.inertiaDeg v)
      (by rw [hyv, hϖ, ← exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]), N.absNorm_eq v, Nat.cast_pow, map_pow]

/-! ### Existence: statement stubs -/

namespace RatIdele

variable (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m)

/-- **The idelic Dirichlet character of $\mathbb Q$**: $\tilde\chi(x) = \chi(r(x))^{-1}$ on
$C_{\mathbb Q} = \mathbb A_{\mathbb Q}^\times/\mathbb Q^\times$ (`ideleChar`, `DirichletHeckeRat.lean`). -/
def ratDirichletChar : HeckeCharacter ℚ :=
  ⟨QuotientGroup.lift _ (ideleChar m χ) (by
      rintro _ ⟨a, rfl⟩
      exact (MonoidHom.mem_ker).mpr (ideleChar_diag m χ a)),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_ideleChar m χ)⟩

theorem ratDirichletChar_mk (x : IdeleGroup (𝓞 ℚ) ℚ) :
    ratDirichletChar m χ (x : IdeleClassGroup (𝓞 ℚ) ℚ) = ideleChar m χ x := rfl

end RatIdele

/-- **The idelic Dirichlet character of $\mathbb Q$ is attached to $\chi$**: $\tilde\chi(x) = \chi(r(x))^{-1}$,
with $r(x)$ the residue mod $m$ of $x/q(x)$, $q(x) = \operatorname{sgn}(x_\infty)\prod_pp^{v_p(x_p)}$. -/
theorem isDirichletLift_ratDirichletChar [NeZero m] (χ : DirichletCharacter ℂ m) :
    IsDirichletLift χ (RatIdele.ratDirichletChar m χ) where
  pow_eq_one n hn := by
    refine ContinuousMonoidHom.ext fun c => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    rw [pow_apply_aux]
    show (RatIdele.ideleChar m χ x) ^ n = 1
    rw [← MonoidHom.pow_apply, RatIdele.ideleChar_pow_eq_one m χ hn]
    rfl
  isUnramifiedAt v hv u hu := by
    rw [RatIdele.absNorm_asIdeal] at hv
    exact RatIdele.ideleChar_unit m χ hv u hu
  finiteComponent_uniformizer v hv ϖ hϖ := by
    rw [RatIdele.absNorm_asIdeal] at hv ⊢
    exact RatIdele.ideleChar_uniformizer m χ hv ϖ hϖ

/-- **The Hecke character of $\mathbb Q$ attached to $\chi$ exists** (for $m = 0$ the conditions at places are
vacuous and $\psi = 1$ works). -/
@[kb "neukirch1999" "Ch. VI, §6 [unverified locator]"]
theorem exists_isDirichletLift_rat (χ : DirichletCharacter ℂ m) :
    ∃ ψ : HeckeCharacter ℚ, IsDirichletLift χ ψ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, fun n _ => one_pow (M := HeckeCharacter ℚ) n, fun v hv => ?_, fun v hv => ?_⟩ <;>
    · exfalso
      rw [Nat.coprime_zero_right, Ideal.absNorm_eq_one_iff] at hv
      exact v.isPrime.ne_top hv
  · have : NeZero m := ⟨hm.ne'⟩
    exact ⟨_, isDirichletLift_ratDirichletChar χ⟩

/-- **Named input: every number field has an idelic norm** $N_{K/\mathbb Q}$ with its local description
(`IdelicNorm K`). Not proved here: $N_{K/\mathbb Q}$
on $\mathbb A_K^\times$ is the determinant of multiplication on $\mathbb A_K\cong\mathbb A_{\mathbb Q}\otimes_{\mathbb Q}K$
(QuadFormsKB's `adeleBaseChange`), and the local description is
$\mathbb Q_p\otimes K\cong\prod_{\mathfrak p\mid p}K_{\mathfrak p}$ with
$v_p(N_{K_{\mathfrak p}/\mathbb Q_p}u) = f(\mathfrak p\mid p)\,v_{\mathfrak p}(u)$. It is quantified over all number
fields because the cyclic case of Chebotarev's theorem applies the cyclotomic case over auxiliary fields $E$ built inside the proof. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on I_L and C_L) [unverified locator]"]
structure IdelicNormInput : Prop where
  nonempty : ∀ (K : Type) [Field K] [NumberField K], Nonempty (IdelicNorm K)

/-- **Existence of $\chi\circ N_{K/\mathbb Q}$**, given an idelic norm of `K`. -/
theorem exists_isDirichletLift_of_idelicNorm (N : IdelicNorm K) (χ : DirichletCharacter ℂ m) :
    ∃ ψ : HeckeCharacter K, IsDirichletLift χ ψ :=
  let ⟨ψ₀, h⟩ := exists_isDirichletLift_rat χ
  ⟨ψ₀.comp N.toHom, h.comp_idelicNorm N⟩

/-- **Existence of $\chi\circ N_{K/\mathbb Q}$**, conditional on the named input `IdelicNormInput`. -/
theorem exists_isDirichletLift (hN : IdelicNormInput) (K : Type) [Field K] [NumberField K]
    (χ : DirichletCharacter ℂ m) : ∃ ψ : HeckeCharacter K, IsDirichletLift χ ψ :=
  exists_isDirichletLift_of_idelicNorm (hN.nonempty K).some χ

end

end NumberFieldKB.Chebotarev
