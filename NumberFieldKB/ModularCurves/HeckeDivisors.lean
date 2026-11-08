import NumberFieldKB.ModularCurves.Ramification

/-!
# The Hecke correspondence $T(p)$ on divisors of $Y_0(N)$ over $\mathbb Q$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §7 (pdf p. 225, D138) and Remark 7.2. The correspondence
$Y_0(N) \xleftarrow{\pi_1} Y_0(pN) \xrightarrow{\pi_p} Y_0(N)$ ($\pi_1 : z \mapsto z$, $\pi_p : z \mapsto pz$) acts
on divisors by $T(p) = \pi_{p*} \circ \pi_1^*$:

* `pullY0`: $\pi^*[P] = \sum_{Q \mid P} e(Q/P)\,[Q]$, over the closed points $Q$ of $Y_0(M)$ above $P$ ($N \mid M$);
* `pushY0`: $\pi_*[Q] = f(Q/\pi Q)\,[\pi Q]$, with the residue degree, for $\pi : z \mapsto dz$, $dN \mid M$;
* `heckeDiv N p := pushY0 ∘ pullY0`.

The degree of a closed point is its residue degree over $\mathbb Q$ (`Y0Point.deg`). Then $\deg \pi_* D = \deg D$
(`deg_pushY0`), $\deg \pi^* D = (\Gamma_0(N) : \Gamma_0(M)) \deg D$ (`deg_pullY0`, from the fundamental identity
`sum_ramification_inertia_forget`), hence **$\deg T(p) D = (\Gamma_0(N) : \Gamma_0(pN)) \deg D$** (`deg_heckeDiv`).
-/

open Polynomial IsDedekindDomain

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The divisors of $Y_0(N)$ over $\mathbb Q$: finite formal sums of closed points. -/
abbrev Y0Div (N : ℕ) [NeZero N] : Type := Y0Point N →₀ ℤ

/-- The **degree** of a closed point of $Y_0(N)$: the degree of its residue field over $\mathbb Q$. -/
noncomputable def Y0Point.deg (P : Y0Point N) : ℕ := P.asIdeal.inertiaDeg ℚ

/-- The degree of a divisor of $Y_0(N)$, $\deg \sum n_P P = \sum n_P \deg P$. -/
noncomputable def Y0Div.deg : Y0Div N →+ ℤ := Finsupp.liftAddHom fun P => zmultiplesHom ℤ (P.deg : ℤ)

theorem Y0Div.deg_single (P : Y0Point N) (n : ℤ) : Y0Div.deg (Finsupp.single P n) = n * P.deg := by
  simp [Y0Div.deg]

/-! ### Push-forward -/

/-- The residue degree $f(Q/\pi Q)$ of a closed point $Q$ of $Y_0(M)$ over its image under $z \mapsto dz$. -/
noncomputable def residueDeg {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) : ℕ :=
  letI := (degeneracyY0 N M d h).toAlgebra
  Q.asIdeal.inertiaDeg (Y0Ring N)

/-- **Push-forward of divisors** along $z \mapsto dz$, $Y_0(M) \to Y_0(N)$: $[Q] \mapsto f(Q/\pi Q)\,[\pi Q]$. -/
noncomputable def pushY0 {d : ℕ} (h : d * N ∣ M) : Y0Div M →+ Y0Div N :=
  Finsupp.liftAddHom fun Q => zmultiplesHom (Y0Div N)
    (Finsupp.single (degeneracyPoint h Q) (residueDeg h Q : ℤ))

theorem pushY0_single {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) (n : ℤ) :
    pushY0 h (Finsupp.single Q n) = Finsupp.single (degeneracyPoint h Q) (n * residueDeg h Q) := by
  simp [pushY0, Finsupp.smul_single]

theorem isScalarTower_rat_degeneracyY0 {d : ℕ} (h : d * N ∣ M) :
    letI := (degeneracyY0 N M d h).toAlgebra
    IsScalarTower ℚ (Y0Ring N) (Y0Ring M) := by
  letI := (degeneracyY0 N M d h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (Y0Ring M))
      ((algebraMap (Y0Ring N) (Y0Ring M)).comp (algebraMap ℚ (Y0Ring N)))) r

/-- The residue degrees multiply: $\deg Q = f(Q/\pi Q) \deg \pi Q$. -/
theorem deg_eq_residueDeg_mul {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) :
    Q.deg = (degeneracyPoint h Q).deg * residueDeg h Q := by
  letI := (degeneracyY0 N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracyY0 h
  haveI : Q.asIdeal.LiesOver (degeneracyPoint h Q).asIdeal := ⟨rfl⟩
  exact Ideal.inertiaDeg_tower (R := ℚ) (degeneracyPoint h Q).asIdeal Q.asIdeal

/-- **Push-forward preserves degrees.** -/
theorem deg_pushY0 {d : ℕ} (h : d * N ∣ M) (D : Y0Div M) : Y0Div.deg (pushY0 h D) = Y0Div.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add]
  | single Q n =>
    rw [pushY0_single, Y0Div.deg_single, Y0Div.deg_single, deg_eq_residueDeg_mul h Q]
    push_cast
    ring

/-! ### Pullback -/

/-- A prime of $\mathcal O(Y_0(M))$ above a closed point $P$ of $Y_0(N)$, as a closed point of $Y_0(M)$. -/
noncomputable def primesOverToPoint (h : 1 * N ∣ M) (P : Y0Point N) :
    letI := forgetY0Algebra N M h
    P.asIdeal.primesOver (Y0Ring M) → Y0Point M :=
  letI := forgetY0Algebra N M h
  fun q => ⟨q.1, q.2.1, by
    haveI : FaithfulSMul (Y0Ring N) (Y0Ring M) :=
      Module.isTorsionFree_iff_faithfulSMul.1 (isTorsionFree_forgetY0 h)
    exact Ideal.ne_bot_of_mem_primesOver P.ne_bot q.2⟩

theorem degeneracyPoint_primesOverToPoint (h : 1 * N ∣ M) (P : Y0Point N)
    (q : letI := forgetY0Algebra N M h; P.asIdeal.primesOver (Y0Ring M)) :
    degeneracyPoint h (primesOverToPoint h P q) = P := by
  letI := forgetY0Algebra N M h
  apply HeightOneSpectrum.ext
  exact (q.2.2.over).symm

/-- **Pullback of divisors** along $z \mapsto z$, $Y_0(M) \to Y_0(N)$ ($N \mid M$):
$[P] \mapsto \sum_{Q \mid P} e(Q/P)\,[Q]$. -/
noncomputable def pullY0 (h : 1 * N ∣ M) : Y0Div N →+ Y0Div M :=
  letI := forgetY0Algebra N M h
  Finsupp.liftAddHom fun P => zmultiplesHom (Y0Div M)
    (letI := fintypePrimesOverY0 h P
     ∑ q : P.asIdeal.primesOver (Y0Ring M),
      Finsupp.single (primesOverToPoint h P q) (q.1.ramificationIdx (Y0Ring N) : ℤ))

/-- **Pullback multiplies degrees by the degree of the map**: $\deg \pi^* D = (\Gamma_0(N) : \Gamma_0(M)) \deg D$. -/
theorem deg_pullY0 (h : 1 * N ∣ M) (D : Y0Div N) :
    Y0Div.deg (pullY0 h D) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) * Y0Div.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add, mul_add]
  | single P n =>
    letI := forgetY0Algebra N M h
    letI := fintypePrimesOverY0 h P
    have hsum := sum_ramification_inertia_forget h P
    simp only [pullY0, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, map_zsmul, map_sum,
      Y0Div.deg_single, smul_eq_mul]
    have hdeg : ∀ q : P.asIdeal.primesOver (Y0Ring M),
        ((q.1.ramificationIdx (Y0Ring N) : ℤ) * ((primesOverToPoint h P q).deg : ℤ)) =
          ((q.1.ramificationIdx (Y0Ring N) * q.1.inertiaDeg (Y0Ring N) : ℕ) : ℤ) * P.deg := by
      intro q
      rw [deg_eq_residueDeg_mul h, degeneracyPoint_primesOverToPoint]
      push_cast
      simp only [residueDeg, primesOverToPoint]
      ring
    rw [Finset.sum_congr rfl fun q _ => hdeg q, ← Finset.sum_mul, ← Nat.cast_sum, hsum]
    ring

/-! ### The Hecke correspondence on divisors -/

/-- **The Hecke correspondence $T(p)$ on divisors of $Y_0(N)$** (Milne V §7, D138; Remark 7.2):
$T(p) = \pi_{p*} \circ \pi_1^*$ for $Y_0(N) \xleftarrow{\pi_1} Y_0(pN) \xrightarrow{\pi_p} Y_0(N)$, i.e.
$T(p)[P] = \sum_{Q \mid P} e(Q/P) f(Q/\pi_p Q)\,[\pi_p Q]$. -/
@[kb "milne2006ec" "Ch. V, §7, the Hecke correspondence T(p) acting on divisors of Y_0(N), pdf p. 225"]
noncomputable def heckeDiv (N p : ℕ) [NeZero N] [NeZero p] : Y0Div N →+ Y0Div N :=
  (pushY0 (d := p) (dvd_rfl : p * N ∣ p * N)).comp (pullY0 (one_mul_dvd_mul N p))

/-- **$\deg T(p) D = (\Gamma_0(N) : \Gamma_0(pN)) \deg D$** ($= (p + 1) \deg D$ for $p \nmid N$). -/
theorem deg_heckeDiv (N p : ℕ) [NeZero N] [NeZero p] (D : Y0Div N) :
    Y0Div.deg (heckeDiv N p D) =
      (CongruenceSubgroup.Gamma0 (p * N)).relIndex (CongruenceSubgroup.Gamma0 N) * Y0Div.deg D := by
  rw [heckeDiv, AddMonoidHom.comp_apply, deg_pushY0, deg_pullY0]

end NumberFieldKB.ModularCurves
