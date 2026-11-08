import NumberFieldKB.ModularCurves.FrickeHecke

/-!
# The Atkin–Lehner involution $w_p$ of $X_0(pN)$ and the symmetry of $T(p)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §4 (pdf p. 205) and §7 (pdf p. 225). For $p \nmid N$ choose
$a, b \in \mathbb Z$ with $pb - aN = 1$ and let
$$W = \begin{pmatrix} p & a \\ pN & pb \end{pmatrix} = \begin{pmatrix} 1 & a \\ N & pb \end{pmatrix}
\begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}, \qquad \det W = p.$$
Then $j \circ W = j_p$, $j_p \circ W = j$, $j_N \circ W = j_{pN}$ and $j_{pN} \circ W = j_N$
(`jFun_atkinLehnerH`, …). So $W$ induces an involution $w_p$ of $\mathbb Q(X_0(pN))$ (`atkinLehnerX0`) which exchanges
the two degeneracy maps $z \mapsto z$ and $z \mapsto pz$ to $X_0(N)$ (`atkinLehnerX0_degeneracy_one`). Consequently:

* **`heckeX0Transpose_eq_heckeX0`**: $T(p)^{\mathsf t} = T(p)$ on divisors of $X_0(N)$ for $p \nmid N$;
* **`frickeDiv_heckeX0_comm`**, **`frickePic0_heckePic0_comm`**: $w_N T(p) = T(p) w_N$ on divisors and on
  $\mathrm{Pic}^0(X_0(N)) = J_0(N)(\mathbb Q)$.

The function-field identities are checked on germs of functions (`toGerm_ringHom_x0Frac`), as in `FrickeHecke.lean`.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex
open scoped MatrixGroups

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.V

/-! ### Germs of $\sigma(f)$ for a ring map $\sigma$ given on $j$ and $j_M$ by a map $w$ of $\mathbb H$ -/

section Germs

variable {M : ℕ} [NeZero M]

/-- If $\sigma(j) = j \circ w$ and $\sigma(j_M) = j_M \circ w$ on germs, then $\sigma(G(j, j_M)) = G(j, j_M) \circ w$. -/
theorem toGerm_ringHom_coordToX0 (σ : X0 M →+* X0 M) (w : ℍ → ℍ)
    (h1 : toGerm M (σ (jX0 (prop2_4' M))) = germ (jFun ∘ w))
    (h2 : toGerm M (σ (jNX0 (prop2_4' M))) = germ (jN M ∘ w)) (G : ℚ[X][X]) :
    toGerm M (σ (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ G))) = germ (evalJJNRat M G ∘ w) := by
  let L : ℚ[X][X] →+* HGerm :=
    (toGerm M).comp (σ.comp ((coordToX0 (prop2_4' M)).comp (Ideal.Quotient.mk _)))
  let R : ℚ[X][X] →+* HGerm := (Filter.Germ.coeRingHom _).comp
    ((RingHom.pi fun z => Pi.evalRingHom (fun _ : ℍ => ℂ) (w z)).comp (evalJJNRat M))
  have hLR : L = R := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · exact RingHom.ext_rat _ _
      · simp only [L, R, RingHom.coe_comp, Function.comp_apply]
        have e : coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ (C X)) = jX0 (prop2_4' M) := rfl
        rw [e, h1]
        congr 1
        funext z
        simp [evalJJNHom]
    · simp only [L, R, RingHom.coe_comp, Function.comp_apply]
      have e : coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ X) = jNX0 (prop2_4' M) := rfl
      rw [e, h2]
      congr 1
      funext z
      simp [evalJJNHom]
  exact RingHom.congr_fun hLR G

/-- The germ of $\sigma(P/Q)$: if $f \cdot Q(j, j_M) = P(j, j_M)$, then $\sigma(P/Q)$ is $f \circ w$. -/
theorem toGerm_ringHom_x0Frac (σ : X0 M →+* X0 M) (w : ℍ → ℍ)
    (h1 : toGerm M (σ (jX0 (prop2_4' M))) = germ (jFun ∘ w))
    (h2 : toGerm M (σ (jNX0 (prop2_4' M))) = germ (jN M ∘ w)) {P Q : ℚ[X][X]} {f : ℍ → ℂ}
    (hQ : evalJJNRat M Q ≠ 0) (hf : ∀ z, f z * evalJJNRat M Q z = evalJJNRat M P z) :
    toGerm M (σ (x0Frac M P Q)) = germ (f ∘ w) := by
  have hQ0 : coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q) ≠ 0 := by
    intro h0
    have h := toGerm_coordToX0 (N := M) Q
    rw [h0, map_zero] at h
    exact (isUnit_germ (mdifferentiable_evalJJNHom _ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) Q) hQ).ne_zero
      h.symm
  have hσQ : σ (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q)) ≠ 0 := (_root_.map_ne_zero σ).2 hQ0
  have hu : IsUnit (toGerm M (σ (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q)))) :=
    (isUnit_iff_ne_zero.2 hσQ).map (toGerm M)
  have hmul : σ (x0Frac M P Q) * σ (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q)) =
      σ (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ P)) := by
    rw [x0Frac, ← map_mul, div_mul_cancel₀ _ hQ0]
  have h3 := congrArg (toGerm M) hmul
  rw [map_mul, toGerm_ringHom_coordToX0 σ w h1 h2, toGerm_ringHom_coordToX0 σ w h1 h2] at h3
  rw [toGerm_ringHom_coordToX0 σ w h1 h2] at hu
  refine hu.mul_left_inj.1 (h3.trans ?_)
  rw [← Filter.Germ.coe_mul]
  congr 1
  funext z
  exact (hf (w z)).symm

end Germs

/-! ### The matrix $W$ acting on $\mathbb H$ -/

section Matrix

variable (p N : ℕ) (a b : ℤ)

/-- $\begin{pmatrix} 1 & a \\ N & pb \end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ for $pb - aN = 1$. -/
def alGamma1 (hab : (p : ℤ) * b - a * N = 1) : SL(2, ℤ) :=
  ⟨!![1, a; (N : ℤ), p * b], by rw [Matrix.det_fin_two_of]; linarith⟩

/-- $\begin{pmatrix} p & a \\ N & b \end{pmatrix} \in \Gamma_0(N)$ for $pb - aN = 1$. -/
def alGamma2 (hab : (p : ℤ) * b - a * N = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ), a; (N : ℤ), b], by rw [Matrix.det_fin_two_of]; linarith⟩

/-- $\begin{pmatrix} 1 & aN \\ 1 & pb \end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ for $pb - aN = 1$. -/
def alGamma3 (hab : (p : ℤ) * b - a * N = 1) : SL(2, ℤ) :=
  ⟨!![1, a * N; 1, p * b], by rw [Matrix.det_fin_two_of]; linarith⟩

/-- The Atkin–Lehner map $W z = (pz + a)/(pNz + pb)$ of $\mathbb H$. -/
noncomputable def atkinLehnerH (hab : (p : ℤ) * b - a * N = 1) (z : ℍ) : ℍ :=
  alGamma1 p N a b hab • ofComplex ((p : ℂ) * z)

variable {p N a b}

theorem alGamma2_mem (hab : (p : ℤ) * b - a * N = 1) : alGamma2 p N a b hab ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [alGamma2]

theorem coe_alGamma1_smul (hab : (p : ℤ) * b - a * N = 1) (u : ℍ) :
    ((alGamma1 p N a b hab • u : ℍ) : ℂ) = (u + a) / (N * u + p * b) := by
  rw [coe_specialLinearGroup_apply]
  simp [alGamma1]

theorem coe_alGamma2_smul (hab : (p : ℤ) * b - a * N = 1) (u : ℍ) :
    ((alGamma2 p N a b hab • u : ℍ) : ℂ) = (p * u + a) / (N * u + b) := by
  rw [coe_specialLinearGroup_apply]
  simp [alGamma2]

theorem coe_alGamma3_smul (hab : (p : ℤ) * b - a * N = 1) (u : ℍ) :
    ((alGamma3 p N a b hab • u : ℍ) : ℂ) = (u + a * N) / (u + p * b) := by
  rw [coe_specialLinearGroup_apply]
  simp [alGamma3]

theorem denom_ne_zero_of_pos {c : ℕ} (hc : 1 ≤ c) (u : ℍ) (r : ℂ) (hr : r.im = 0) : (c : ℂ) * u + r ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, mul_im, natCast_re, natCast_im, coe_re, coe_im, zero_mul, add_zero, hr, zero_im] at this
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  exact (mul_pos hc' u.im_pos).ne' this

variable (hp : 1 ≤ p) (hN : 1 ≤ N) (hab : (p : ℤ) * b - a * N = 1)
include hp hN

omit hN in
theorem coe_atkinLehnerH (z : ℍ) :
    (atkinLehnerH p N a b hab z : ℂ) = (p * z + a) / (p * N * z + p * b) := by
  rw [atkinLehnerH, coe_alGamma1_smul, coe_ofComplex_mul hp]
  ring_nf

omit hp hN in
/-- $j(Wz) = j(pz)$. -/
theorem jFun_atkinLehnerH (z : ℍ) : jFun (atkinLehnerH p N a b hab z) = jN p z := by
  rw [atkinLehnerH, jFun_smul]
  rfl

/-- $j_p(Wz) = j(z)$. -/
theorem jN_p_atkinLehnerH (z : ℍ) : jN p (atkinLehnerH p N a b hab z) = jFun z := by
  have e : ofComplex ((p : ℂ) * (atkinLehnerH p N a b hab z : ℂ)) = alGamma2 p N a b hab • z := by
    ext
    rw [coe_ofComplex_mul hp, coe_alGamma2_smul, coe_atkinLehnerH hp hab]
    have h1 := denom_ne_zero_of_pos hN z (b : ℂ) (by simp)
    have h2 : (p : ℂ) * N * z + p * b ≠ 0 := by
      have := denom_ne_zero_of_pos (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)) :
        1 ≤ p * N) z ((p : ℂ) * b) (by simp)
      simpa using this
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    field_simp
  unfold jN
  rw [e, jFun_smul]

/-- $j_{pN}(Wz) = j_N(z)$. -/
theorem jN_pN_atkinLehnerH (z : ℍ) : jN (p * N) (atkinLehnerH p N a b hab z) = jN N z := by
  rw [← jN_smul hN (alGamma2_mem hab) z]
  unfold jN
  congr 2
  rw [coe_alGamma2_smul, coe_atkinLehnerH hp hab]
  have h1 := denom_ne_zero_of_pos hN z (b : ℂ) (by simp)
  have h2 : (p : ℂ) * N * z + p * b ≠ 0 := by
    have := denom_ne_zero_of_pos (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)) :
      1 ≤ p * N) z ((p : ℂ) * b) (by simp)
    simpa using this
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  push_cast
  field_simp

/-- $j_N(Wz) = j_{pN}(z)$. -/
theorem jN_N_atkinLehnerH (z : ℍ) : jN N (atkinLehnerH p N a b hab z) = jN (p * N) z := by
  have hpN : 1 ≤ p * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : ofComplex ((N : ℂ) * (atkinLehnerH p N a b hab z : ℂ)) =
      alGamma3 p N a b hab • ofComplex (((p * N : ℕ) : ℂ) * z) := by
    ext
    rw [coe_ofComplex_mul hN, coe_alGamma3_smul, coe_ofComplex_mul hpN, coe_atkinLehnerH hp hab]
    have h2 : (p : ℂ) * N * z + p * b ≠ 0 := by
      have := denom_ne_zero_of_pos hpN z ((p : ℂ) * b) (by simp)
      simpa using this
    push_cast
    field_simp
  unfold jN
  rw [e, jFun_smul]

end Matrix

/-! ### The involution $w_p$ of $\mathbb Q(X_0(pN))$ -/

section Field

variable {p N : ℕ} [NeZero p] [NeZero N] {a b : ℤ}

theorem one_le_neZero (n : ℕ) [NeZero n] : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)

theorem exists_atkinLehnerX0 (hab : (p : ℤ) * b - a * N = 1) :
    ∃ σ : X0 (p * N) →+* X0 (p * N), σ (jX0 (prop2_4' (p * N))) = jNElt (p * N) p (dvd_mul_right p N) ∧
      σ (jNX0 (prop2_4' (p * N))) = jNElt (p * N) N (dvd_mul_left N p) :=
  exists_embedding (N := p * N) (M := p * N) (toGerm_jNElt _) (toGerm_jNElt _)
    (jN_mdifferentiable (one_le_neZero p)) (jN_surjective (one_le_neZero p)) fun z => by
      have h := (prop2_4' (p * N)).exists_poly.choose_spec.2.2.1 (atkinLehnerH p N a b hab z)
      unfold evalJJN at h
      rw [jFun_atkinLehnerH, jN_pN_atkinLehnerH (one_le_neZero p) (one_le_neZero N) hab] at h
      exact h

/-- The ring map $f \mapsto f \circ W$ of $\mathbb Q(X_0(pN))$: $j \mapsto j_p$, $j_{pN} \mapsto j_N$. -/
noncomputable def atkinLehnerHom (hab : (p : ℤ) * b - a * N = 1) : X0 (p * N) →+* X0 (p * N) :=
  (exists_atkinLehnerX0 hab).choose

theorem atkinLehnerHom_jX0 (hab : (p : ℤ) * b - a * N = 1) :
    atkinLehnerHom hab (jX0 (prop2_4' (p * N))) = jNElt (p * N) p (dvd_mul_right p N) :=
  (exists_atkinLehnerX0 hab).choose_spec.1

theorem atkinLehnerHom_jNX0 (hab : (p : ℤ) * b - a * N = 1) :
    atkinLehnerHom hab (jNX0 (prop2_4' (p * N))) = jNElt (p * N) N (dvd_mul_left N p) :=
  (exists_atkinLehnerX0 hab).choose_spec.2

theorem toGerm_atkinLehnerHom_jNElt (hab : (p : ℤ) * b - a * N = 1) {d : ℕ} (hd : d ∣ p * N) :
    toGerm (p * N) (atkinLehnerHom hab (jNElt (p * N) d hd)) = germ (jN d ∘ atkinLehnerH p N a b hab) := by
  have hp := one_le_neZero p
  have hN := one_le_neZero N
  have h1 : toGerm (p * N) (atkinLehnerHom hab (jX0 (prop2_4' (p * N)))) =
      germ (jFun ∘ atkinLehnerH p N a b hab) := by
    rw [atkinLehnerHom_jX0, toGerm_jNElt]
    congr 1
    funext z
    exact (jFun_atkinLehnerH hab z).symm
  have h2 : toGerm (p * N) (atkinLehnerHom hab (jNX0 (prop2_4' (p * N)))) =
      germ (jN (p * N) ∘ atkinLehnerH p N a b hab) := by
    rw [atkinLehnerHom_jNX0, toGerm_jNElt]
    congr 1
    funext z
    exact (jN_pN_atkinLehnerH hp hN hab z).symm
  rw [jNElt]
  exact toGerm_ringHom_x0Frac _ _ h1 h2 (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.1
    (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.2

theorem jNElt_self (M : ℕ) [NeZero M] (h : M ∣ M) : jNElt M M h = jNX0 (prop2_4' M) := by
  apply toGerm_injective (N := M)
  rw [toGerm_jNElt, toGerm_jNX0]

theorem atkinLehnerHom_atkinLehnerHom (hab : (p : ℤ) * b - a * N = 1) (x : X0 (p * N)) :
    atkinLehnerHom hab (atkinLehnerHom hab x) = x := by
  have hp := one_le_neZero p
  have hN := one_le_neZero N
  have key : (atkinLehnerHom hab).comp (atkinLehnerHom hab) = RingHom.id _ := by
    apply X0.ringHom_ext
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [atkinLehnerHom_jX0]
      apply toGerm_injective (N := p * N)
      rw [toGerm_atkinLehnerHom_jNElt, toGerm_jX0]
      congr 1
      funext z
      exact jN_p_atkinLehnerH hp hN hab z
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [atkinLehnerHom_jNX0]
      apply toGerm_injective (N := p * N)
      rw [toGerm_atkinLehnerHom_jNElt, toGerm_jNX0]
      congr 1
      funext z
      exact jN_N_atkinLehnerH hp hN hab z
  exact RingHom.congr_fun key x

/-- **The Atkin–Lehner involution $w_p$ of $\mathbb Q(X_0(pN))$**, $f \mapsto f \circ W$, for $pb - aN = 1$. -/
@[kb "milne2006ec" "Ch. V, §4, the Atkin-Lehner involution w_p of X_0(pN) for p ∤ N (running text), pdf p. 205"]
noncomputable def atkinLehnerX0 (hab : (p : ℤ) * b - a * N = 1) : X0 (p * N) ≃+* X0 (p * N) :=
  RingEquiv.ofRingHom (atkinLehnerHom hab) (atkinLehnerHom hab)
    (RingHom.ext (atkinLehnerHom_atkinLehnerHom hab)) (RingHom.ext (atkinLehnerHom_atkinLehnerHom hab))

/-- **$w_p$ exchanges the two degeneracy maps**: $w_p^* \iota_1 = \iota_p$ (on curves, $\pi_1 \circ w_p = \pi_p$). -/
theorem atkinLehnerX0_degeneracy_one (hab : (p : ℤ) * b - a * N = 1) (x : X0 N) :
    atkinLehnerX0 hab (degeneracy N (p * N) 1 (one_mul_dvd_mul N p) x) = degeneracy N (p * N) p dvd_rfl x := by
  have hp := one_le_neZero p
  have hN := one_le_neZero N
  have key : (atkinLehnerHom hab).comp (degeneracy N (p * N) 1 (one_mul_dvd_mul N p)) =
      degeneracy N (p * N) p dvd_rfl := by
    apply X0.ringHom_ext
    · rw [RingHom.comp_apply, degeneracy_jX0, degeneracy_jX0, jNElt_one, atkinLehnerHom_jX0]
    · rw [RingHom.comp_apply, degeneracy_jNX0, degeneracy_jNX0]
      apply toGerm_injective (N := p * N)
      rw [toGerm_atkinLehnerHom_jNElt, toGerm_jNElt]
      congr 1
      funext z
      simp only [Function.comp_apply, one_mul]
      exact jN_N_atkinLehnerH hp hN hab z
  exact RingHom.congr_fun key x

theorem intertwines_atkinLehner (hab : (p : ℤ) * b - a * N = 1) :
    Intertwines (one_mul_dvd_mul N p) (dvd_rfl : p * N ∣ p * N) (atkinLehnerX0 hab) (RingEquiv.refl (X0 N)) :=
  ⟨atkinLehnerHom_atkinLehnerHom hab, fun _ => rfl, atkinLehnerX0_degeneracy_one hab⟩

end Field

/-! ### $T(p)$ is symmetric for $p \nmid N$, and commutes with $w_N$ -/

section Symmetry

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.comapEquiv_refl (Q : PrimeDivisor ℚ K) :
    Q.comapEquiv (RingEquiv.refl K) = Q := by
  apply PrimeDivisor.ext_O
  ext x
  rw [PrimeDivisor.mem_comapEquiv_O]
  rfl

theorem divComapEquiv_refl (D : Divisor ℚ K) : divComapEquiv (RingEquiv.refl K) D = D := by
  ext Q
  rw [divComapEquiv_apply (fun _ => rfl), PrimeDivisor.comapEquiv_refl]

variable {p N : ℕ} [NeZero p] [NeZero N]

omit [NeZero p] [NeZero N] in
theorem exists_bezout (hpN : Nat.Coprime p N) : ∃ a b : ℤ, (p : ℤ) * b - a * N = 1 := by
  have h := Nat.gcd_eq_gcd_ab p N
  rw [hpN] at h
  exact ⟨-Nat.gcdB p N, Nat.gcdA p N, by push_cast at h; linarith⟩

/-- **$T(p)$ is symmetric** for $p \nmid N$: $T(p)^{\mathsf t} = \pi_{1*}\pi_p^* = \pi_{p*}\pi_1^* = T(p)$ on divisors of
$X_0(N)$, cusps included. -/
@[kb "milne2006ec" "Ch. V, §7, T(p) as a symmetric correspondence on X_0(N) for p ∤ N, pdf p. 225"]
theorem heckeX0Transpose_eq_heckeX0 (hpN : Nat.Coprime p N) : heckeX0Transpose N p = heckeX0 N p := by
  obtain ⟨a, b, hab⟩ := exists_bezout hpN
  have H := intertwines_atkinLehner hab
  refine AddMonoidHom.ext fun D => ?_
  rw [heckeX0Transpose, heckeX0, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    ← divComapEquiv_refl (pushX0 dvd_rfl _), divComapEquiv_pushX0 H.symm, divComapEquiv_pullX0 H,
    divComapEquiv_refl]

/-- **$w_N$ commutes with $T(p)$** on divisors of $X_0(N)$ for $p \nmid N$. -/
@[kb "milne2006ec" "Ch. V, §4, w_N commutes with T(p) for p ∤ N, pdf p. 205"]
theorem frickeDiv_heckeX0_comm (hpN : Nat.Coprime p N) (D : Divisor ℚ (X0 N)) :
    frickeDiv N (heckeX0 N p D) = heckeX0 N p (frickeDiv N D) := by
  have h := frickeDiv_heckeX0_frickeDiv N p (frickeDiv N D)
  rw [frickeDiv_frickeDiv, heckeX0Transpose_eq_heckeX0 hpN] at h
  exact h

/-- **$T(p)$ on $J_0(N)(\mathbb Q)$ is symmetric** for $p \nmid N$. -/
theorem heckePic0Transpose_eq_heckePic0 (hpN : Nat.Coprime p N) :
    heckePic0Transpose N p = heckePic0 N p := by
  refine AddMonoidHom.ext fun c => ?_
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    rw [heckePic0Transpose, pic0Map_mk, heckePic0_mk]
    congr 1
    exact Subtype.ext (show heckeX0Transpose N p D.1 = heckeX0 N p D.1 by rw [heckeX0Transpose_eq_heckeX0 hpN])

/-- **$w_N$ commutes with $T(p)$ on $J_0(N)(\mathbb Q) = \mathrm{Pic}^0(X_0(N))$** for $p \nmid N$. -/
@[kb "milne2006ec" "Ch. V, §4 and §7, w_N commutes with T(p) on J_0(N) for p ∤ N, pdf pp. 205, 225"]
theorem frickePic0_heckePic0_comm (hpN : Nat.Coprime p N) (c : Pic0X0 N) :
    frickePic0 N (heckePic0 N p c) = heckePic0 N p (frickePic0 N c) := by
  have h := frickePic0_heckePic0_frickePic0 N p (frickePic0 N c)
  rw [frickePic0_frickePic0, heckePic0Transpose_eq_heckePic0 hpN] at h
  exact h

end Symmetry

end NumberFieldKB.ModularCurves
