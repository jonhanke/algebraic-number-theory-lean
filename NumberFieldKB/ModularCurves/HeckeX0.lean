import NumberFieldKB.ModularCurves.PlaceMaps
import NumberFieldKB.ModularCurves.DivisorsX0

/-!
# The Hecke correspondence $T(p)$ on divisors of $X_0(N)$ over $\mathbb Q$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §7 (pdf p. 225, D138; Remark 7.1: correspondences on the
affine curves extend to the projective curves). The points of $X_0(N)$ over $\mathbb Q$ are the places of
$\mathbb Q(X_0(N))$, cusps included (`placeEquiv`); divisors are Milne's `MilneEC.Divisor ℚ (X0 N)`.

* `degeneracyPlace h Q`: the image of a place $Q$ of $X_0(M)$ under $z \mapsto dz$ ($dN \mid M$).
* `pushX0`: push-forward $[Q] \mapsto f(Q/\pi Q)[\pi Q]$ along $z \mapsto dz$; it preserves degrees (`deg_pushX0`).
* `placesAbove h P`: the finitely many places of $X_0(M)$ over a place $P$ of $X_0(N)$ for $z \mapsto z$
  (finite because they are among the zeros of a uniformizer at $P$, `finite_not_isUnitAt_X0`).
* `pullX0`: pullback $[P] \mapsto \sum_{Q \mid P} e(Q/P)[Q]$, $e(Q/P) = \operatorname{ord}_Q(t_P)$.
* **`heckeX0 N p`** $= \pi_{p*} \circ \pi_1^*$: $T(p)$ on divisors of $X_0(N)$.
-/

open Polynomial IsDedekindDomain

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem isScalarTower_rat_degeneracy {d : ℕ} (h : d * N ∣ M) :
    letI := (degeneracy N M d h).toAlgebra
    IsScalarTower ℚ (X0 N) (X0 M) := by
  letI := (degeneracy N M d h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (X0 M)) ((algebraMap (X0 N) (X0 M)).comp
      (algebraMap ℚ (X0 N)))) r

/-- **The map $X_0(M) \to X_0(N)$, $z \mapsto dz$, on points** (places, cusps included). -/
noncomputable def degeneracyPlace {d : ℕ} (h : d * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) : PrimeDivisor ℚ (X0 N) :=
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  Q.comap

theorem mem_degeneracyPlace_O {d : ℕ} (h : d * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) (x : X0 N) :
    x ∈ (degeneracyPlace h Q).O ↔ degeneracy N M d h x ∈ Q.O := by
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  exact Q.mem_comap_O x

/-- **Push-forward of divisors of $X_0$ along $z \mapsto dz$**: $[Q] \mapsto f(Q/\pi Q)\,[\pi Q]$. -/
noncomputable def pushX0 {d : ℕ} (h : d * N ∣ M) : Divisor ℚ (X0 M) →+ Divisor ℚ (X0 N) :=
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  pushDiv

theorem deg_pushX0 {d : ℕ} (h : d * N ∣ M) (D : Divisor ℚ (X0 M)) :
    Divisor.deg (pushX0 h D) = Divisor.deg D := by
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  exact deg_pushDiv D

/-- A uniformizer is not a unit of its valuation ring. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.unif_inv_not_mem (P : PrimeDivisor ℚ (X0 N)) : P.unif⁻¹ ∉ P.O := by
  obtain ⟨t, ht, e⟩ := P.exists_uniO
  intro hinv
  have ht0 : (t : X0 N) ≠ 0 := fun h0 => ht.ne_zero (Subtype.ext h0)
  apply ht.not_isUnit
  rw [← e] at hinv
  exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : P.O) (Subtype.ext (by simp [ht0]))

/-- **Finitely many places of $X_0(M)$ lie over a place of $X_0(N)$** (for $z \mapsto dz$). -/
theorem finite_degeneracyPlace_eq {d : ℕ} (h : d * N ∣ M) (P : PrimeDivisor ℚ (X0 N)) :
    {Q : PrimeDivisor ℚ (X0 M) | degeneracyPlace h Q = P}.Finite := by
  refine (finite_not_isUnitAt_X0 (N := M) (degeneracy N M d h P.unif)).subset fun Q hQ hu => ?_
  have hQ' : degeneracyPlace h Q = P := hQ
  have key : P.unif⁻¹ ∈ (degeneracyPlace h Q).O := by
    rw [mem_degeneracyPlace_O, map_inv₀]
    exact hu.2
  rw [hQ'] at key
  exact P.unif_inv_not_mem key

/-- The places of $X_0(M)$ over a place $P$ of $X_0(N)$, for $z \mapsto dz$. -/
noncomputable def placesAbove {d : ℕ} (h : d * N ∣ M) (P : PrimeDivisor ℚ (X0 N)) :
    Finset (PrimeDivisor ℚ (X0 M)) :=
  (finite_degeneracyPlace_eq h P).toFinset

theorem mem_placesAbove {d : ℕ} (h : d * N ∣ M) (P : PrimeDivisor ℚ (X0 N)) (Q : PrimeDivisor ℚ (X0 M)) :
    Q ∈ placesAbove h P ↔ degeneracyPlace h Q = P := by
  simp [placesAbove]

/-- The ramification index $e(Q/P) = \operatorname{ord}_Q(t_P)$, $t_P$ a uniformizer at $P$. -/
noncomputable def ramIndex {d : ℕ} (h : d * N ∣ M) (P : PrimeDivisor ℚ (X0 N)) (Q : PrimeDivisor ℚ (X0 M)) :
    ℤ :=
  Q.ord (degeneracy N M d h P.unif)

/-- **Pullback of divisors of $X_0$ along $z \mapsto dz$**: $[P] \mapsto \sum_{Q \mid P} e(Q/P)\,[Q]$. -/
noncomputable def pullX0 {d : ℕ} (h : d * N ∣ M) : Divisor ℚ (X0 N) →+ Divisor ℚ (X0 M) :=
  Finsupp.liftAddHom fun P => zmultiplesHom (Divisor ℚ (X0 M))
    (∑ Q ∈ placesAbove h P, Finsupp.single Q (ramIndex h P Q))

/-- **The Hecke correspondence $T(p)$ on divisors of $X_0(N)$** (Milne V §7, D138, Remark 7.1):
$T(p) = \pi_{p*} \circ \pi_1^*$ for $X_0(N) \xleftarrow{\pi_1} X_0(pN) \xrightarrow{\pi_p} X_0(N)$, on all points of
$X_0(N)$ over $\mathbb Q$, cusps included. -/
@[kb "milne2006ec" "Ch. V, §7, the Hecke correspondence T(p) on divisors of X_0(N), Remark 7.1, pdf p. 225"]
noncomputable def heckeX0 (N p : ℕ) [NeZero N] [NeZero p] : Divisor ℚ (X0 N) →+ Divisor ℚ (X0 N) :=
  (pushX0 (d := p) (dvd_rfl : p * N ∣ p * N)).comp (pullX0 (d := 1) (one_mul_dvd_mul N p))

end NumberFieldKB.ModularCurves
