import NumberFieldKB.ModularCurves.Cusps
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Divisors of functions on $X_0(N)$ over $\mathbb Q$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 (pdf pp. 44–45) and Ch. V, §2. A nonzero function on the
nonsingular projective curve $X_0(N)$ over $\mathbb Q$ has only finitely many zeros and poles, so it has a divisor
in Milne's sense (`MilneEC.IsDivisorOf`): `exists_isDivisorOf_X0`. The proof covers $X_0(N)$ by its two smooth affine
charts, $Y_0(N)$ (`Y0Ring N`, the places where $j$ is finite) and the chart at the cusps (`cuspRing N`, the places
where $1/j$ is finite), each a Dedekind domain, and uses the finiteness of the support of an element of the
field of fractions of a Dedekind domain (Mathlib's `HeightOneSpectrum.Support.finite`).

The degree of the divisor of a function is 0 (the product formula). That is not proved here; for function fields
over an arbitrary constant field it is `TauCeti.Divisor.degree_principal` (Tau Ceti,
`TauCeti/FieldTheory/FunctionField/Divisor/ProductFormula.lean`), not importable here.
-/

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

section General

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra ℚ K]

/-- A place `p` at which `h` is a unit: $h, h^{-1} \in \mathcal O_p$. -/
def _root_.NumberFieldKB.MilneEC.PrimeDivisor.IsUnitAt {k : Type*} [Field k] [Algebra k K]
    (p : PrimeDivisor k K) (h : K) : Prop :=
  h ∈ p.O ∧ h⁻¹ ∈ p.O

/-- **Finiteness on one chart**: among the places containing a Dedekind domain `R`, only finitely many fail to
make a given `h` a unit. -/
theorem finite_not_isUnitAt (hk : ∀ c : ℚ, ∃ r : R, algebraMap R K r = algebraMap ℚ K c) (h : K) :
    {p : PrimeDivisor ℚ K | (∀ r : R, algebraMap R K r ∈ p.O) ∧ ¬ p.IsUnitAt h}.Finite := by
  apply ((HeightOneSpectrum.Support.finite R h).union (HeightOneSpectrum.Support.finite R h⁻¹)).image
    (HeightOneSpectrum.toPrimeDivisor ℚ hk) |>.subset
  rintro p ⟨hR, hu⟩
  obtain ⟨v, rfl⟩ := (exists_toPrimeDivisor_iff hk p).2 hR
  refine ⟨v, ?_, rfl⟩
  simp only [PrimeDivisor.IsUnitAt, HeightOneSpectrum.toPrimeDivisor, mem_valuationSubringAtPrime_iff,
    not_and_or, not_le] at hu
  rcases hu with hu | hu
  · exact Or.inl hu
  · exact Or.inr hu

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] in
/-- Integrality over $\mathbb Q[t]$ forces membership in any valuation ring containing $t$. -/
theorem mem_O_of_isIntegral' [Algebra ℚ[X] K] (p : PrimeDivisor ℚ K) {t : K} (ht : t ∈ p.O)
    (hA : algebraMap ℚ[X] K = eval₂RingHom (algebraMap ℚ K) t) {x : K} (hx : IsIntegral ℚ[X] x) :
    x ∈ p.O := by
  let φ : ℚ[X] →+* p.O := eval₂RingHom p.ofBase ⟨t, ht⟩
  have hc : (algebraMap p.O K).comp φ = algebraMap ℚ[X] K := by
    rw [hA]
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat (((algebraMap p.O K).comp φ).comp C)
        ((eval₂RingHom (algebraMap ℚ K) t).comp C)) a
    · simp [φ]
  obtain ⟨f, hfm, hf⟩ := hx
  have hint : IsIntegral p.O x := ⟨f.map φ, hfm.map φ, by rw [eval₂_map, hc]; exact hf⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := p.O) (K := K)).1 hint
  rw [← hy]
  exact y.2

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra ℚ K] in
/-- Milne's $\operatorname{ord}_p(h)$ vanishes where `h` is a unit. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_eq_zero_of_isUnitAt {k : Type*} [Field k]
    [Algebra k K] (p : PrimeDivisor k K) {h : K} (hu : p.IsUnitAt h) : p.ord h = 0 := by
  by_cases h0 : h = 0
  · subst h0
    unfold PrimeDivisor.ord
    split_ifs with H
    · obtain ⟨u, hu⟩ := H.choose_spec
      exfalso
      have hunif : p.unif ≠ 0 := by
        obtain ⟨t, ht, e⟩ := p.exists_uniO
        rw [← e]
        exact fun h => ht.ne_zero (Subtype.ext h)
      have hu0 : ((u : p.O) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      exact (mul_ne_zero hu0 (zpow_ne_zero _ hunif)) hu.symm
    · rfl
  · have hmul : (⟨h, hu.1⟩ : p.O) * ⟨h⁻¹, hu.2⟩ = 1 := Subtype.ext (by simp [h0])
    let u : p.Oˣ := ⟨⟨h, hu.1⟩, ⟨h⁻¹, hu.2⟩, hmul, by rw [mul_comm]; exact hmul⟩
    exact PrimeDivisor.ord_eq_of_rep p (u := u) (n := 0) (by simp [u])

end General

variable {N : ℕ} [NeZero N]

theorem algebraMap_polyX0_eq' :
    algebraMap ℚ[X] (X0 N) = eval₂RingHom (algebraMap ℚ (X0 N)) (jX0 (prop2_4' N)) := by
  rw [algebraMap_polyX0_eq]
  rfl

theorem algebraMap_polyXInf_eq :
    algebraMap ℚ[X] (XInf N) = eval₂RingHom (algebraMap ℚ (XInf N)) (toXInf (jX0 (prop2_4' N))⁻¹) := by
  refine RingHom.ext fun q => ?_
  change ratFuncLift (L := X0 N) _ injective_eval₂RingHom_jX0_inv (algebraMap ℚ[X] (RatFunc ℚ) q) = _
  rw [ratFuncLift_algebraMap]
  congr 1

theorem exists_cuspRing_eq_algebraMap (c : ℚ) :
    ∃ r : cuspRing N, algebraMap (cuspRing N) (XInf N) r = algebraMap ℚ (XInf N) c := by
  refine ⟨algebraMap ℚ[X] (cuspRing N) (C c), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, algebraMap_polyXInf_eq]
  simp

/-- At a place where $1/j$ is finite, the whole chart at the cusps is regular. -/
theorem mem_O_of_cuspRing (p : PrimeDivisor ℚ (X0 N)) (hj : (jX0 (prop2_4' N))⁻¹ ∈ p.O) (r : cuspRing N) :
    (r : XInf N) ∈ (p : PrimeDivisor ℚ (XInf N)).O := by
  let p' : PrimeDivisor ℚ (XInf N) := p
  exact mem_O_of_isIntegral' p' (t := toXInf (jX0 (prop2_4' N))⁻¹) hj algebraMap_polyXInf_eq r.2

/-- **A nonzero function on $X_0(N)$ is a unit at all but finitely many places** (both charts). -/
theorem finite_not_isUnitAt_X0 (h : X0 N) :
    {p : PrimeDivisor ℚ (X0 N) | ¬ p.IsUnitAt h}.Finite := by
  have h1 := finite_not_isUnitAt (R := Y0Ring N) (K := X0 N) exists_Y0_eq_algebraMap h
  have h2 := finite_not_isUnitAt (R := cuspRing N) (K := XInf N) exists_cuspRing_eq_algebraMap (toXInf h)
  refine (h1.union h2).subset fun p hp => ?_
  by_cases hj : jX0 (prop2_4' N) ∈ p.O
  · exact Or.inl ⟨fun r => mem_O_of_isIntegral' p hj algebraMap_polyX0_eq' r.2, hp⟩
  · have hj' : (jX0 (prop2_4' N))⁻¹ ∈ p.O := by
      rcases p.O.mem_or_inv_mem (jX0 (prop2_4' N)) with h | h
      · exact absurd h hj
      · exact h
    exact Or.inr ⟨mem_O_of_cuspRing p hj', hp⟩

/-- **Every nonzero function on $X_0(N)$ has a divisor** (Milne Ch. I, §4, p. 45): only finitely many places are
zeros or poles. -/
@[kb "milne2006ec" "Ch. I, §4, div(h) is a divisor, for X_0(N) over Q, pdf p. 45"]
theorem exists_isDivisorOf_X0 {h : X0 N} (h0 : h ≠ 0) : ∃ D : Divisor ℚ (X0 N), IsDivisorOf D h := by
  have hfin : (Function.support fun p : PrimeDivisor ℚ (X0 N) => p.ord h).Finite :=
    (finite_not_isUnitAt_X0 h).subset fun p hp => fun hu => hp (p.ord_eq_zero_of_isUnitAt hu)
  exact ⟨Finsupp.ofSupportFinite _ hfin, h0, fun p => rfl⟩

/-- The group $\mathrm{Pic}^0(X_0(N))$ over $\mathbb Q$ (Milne Ch. I, §4, p. 42, `MilneEC.Pic0`): degree-zero
divisors modulo divisors of functions. By `exists_isDivisorOf_X0` every nonzero function contributes its divisor.
When $X_0(N)$ has a rational point (the cusp $\infty$), this is the group $J_0(N)(\mathbb Q)$ of rational points
of the jacobian; the jacobian as an abelian variety over $\mathbb Q$ is not formalized. -/
@[kb "milne2006ec" "Ch. V, §6, J_0(N) (its rational points as Pic^0 of X_0(N)) (running text), pdf p. 222"]
abbrev Pic0X0 (N : ℕ) [NeZero N] : Type := Pic0 ℚ (X0 N)

end NumberFieldKB.ModularCurves
