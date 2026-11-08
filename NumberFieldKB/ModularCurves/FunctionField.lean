import NumberFieldKB.ModularCurves.Rationality
import NumberFieldKB.ModularCurves.Fricke
import NumberFieldKB.ModularCurves.ConstantField

/-!
# The function field $\mathbb Q(X_0(N))$
J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 (pdf pp. 193–195). With Proposition 2.4 now proved
(`prop2_4`), the results on the plane model $F_N(X, Y) = 0$ hold for every $N \ge 1$. This file

* identifies `X0Field h` $= \mathbb Q(X)[Y]/(F_N)$ with the field of fractions of the coordinate ring
  $\mathbb Q[X, Y]/(F_N)$ (`coordToX0`, `isFractionRing_coordToX0`, `x0FieldEquivFractionRing`);
* proves that $\mathbb Q$ is algebraically closed in `X0Field h` (`X0Field.eq_algebraMap_of_isAlgebraic`), so
  $\mathbb Q$ is the exact constant field of $X_0(N)$;
* extends the Fricke involution $w_N$ ($j \leftrightarrow j_N$, `frickeCoord`) to a field automorphism of order
  at most $2$ of `X0Field h` (`frickeX0`);
* fixes the unconditional objects `modPoly N`, `X0 N`, `coordRingX0 N` for `[NeZero N]`.
-/

open Polynomial
open UpperHalfPlane hiding I

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N : ℕ}

/-! ### The coordinate ring inside the function field -/

/-- The inclusion $\mathbb Q[X, Y]/(F_N) \to \mathbb Q(X)[Y]/(F_N)$. -/
noncomputable def coordToX0 (h : Prop2_4 N) : coordRing h →+* X0Field h :=
  Ideal.Quotient.lift _ ((AdjoinRoot.mk _).comp (mapRingHom (algebraMap ℚ[X] (RatFunc ℚ)))) fun G hG => by
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.1 hG
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul, map_mul, AdjoinRoot.mk_self,
      mul_zero]

theorem coordToX0_mk (h : Prop2_4 N) (G : ℚ[X][X]) :
    coordToX0 h (Ideal.Quotient.mk _ G) = AdjoinRoot.mk _ (G.map (algebraMap ℚ[X] (RatFunc ℚ))) := rfl

theorem coordToX0_injective (h : Prop2_4 N) : Function.Injective (coordToX0 h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coordToX0_mk, AdjoinRoot.mk_eq_zero] at hx
  have hm := modPolyQ_monic h
  have hinj : Function.Injective (algebraMap ℚ[X] (RatFunc ℚ)) := IsFractionRing.injective _ _
  have h1 : (G %ₘ modPolyQ h).map (algebraMap ℚ[X] (RatFunc ℚ)) = 0 := by
    rw [map_modByMonic _ hm]
    exact (modByMonic_eq_zero_iff_dvd (hm.map _)).2 hx
  have h2 : G %ₘ modPolyQ h = 0 := by
    rw [← Polynomial.map_zero (algebraMap ℚ[X] (RatFunc ℚ))] at h1
    exact Polynomial.map_injective _ hinj h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact (modByMonic_eq_zero_iff_dvd hm).1 h2

theorem coordToX0_C (h : Prop2_4 N) (d : ℚ[X]) :
    coordToX0 h (Ideal.Quotient.mk _ (C d)) = AdjoinRoot.of _ (algebraMap ℚ[X] (RatFunc ℚ) d) := by
  rw [coordToX0_mk, Polynomial.map_C]
  rfl

theorem coordToX0_C_ne_zero (h : Prop2_4 N) [NeZero N] {d : ℚ[X]} (hd : d ≠ 0) :
    coordToX0 h (Ideal.Quotient.mk _ (C d)) ≠ 0 := by
  rw [coordToX0_C]
  exact (map_ne_zero_iff _ (AdjoinRoot.of ((modPolyQ h).map (algebraMap ℚ[X] (RatFunc ℚ)))).injective).2
    ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 hd)

theorem coordToX0_CC (h : Prop2_4 N) (q : ℚ) :
    coordToX0 h (Ideal.Quotient.mk _ (C (C q))) = algebraMap ℚ (X0Field h) q := by
  rw [coordToX0_mk, Polynomial.map_C, RatFunc.algebraMap_C,
    IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) (X0Field h), AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
    show RatFunc.C q = algebraMap ℚ (RatFunc ℚ) q from RingHom.congr_fun (RingHom.ext_rat _ _) q]

/-- Every element of $\mathbb Q(X_0(N))$ is a quotient $G(X, Y)/d(X)$ with $G \in \mathbb Q[X, Y]$ and
$0 \ne d \in \mathbb Q[X]$. -/
theorem exists_eq_div (h : Prop2_4 N) [NeZero N] (z : X0Field h) :
    ∃ (G : ℚ[X][X]) (d : ℚ[X]), d ≠ 0 ∧
      z = coordToX0 h (Ideal.Quotient.mk _ G) / coordToX0 h (Ideal.Quotient.mk _ (C d)) := by
  induction z using AdjoinRoot.induction_on with
  | ih P =>
    obtain ⟨b, hb, hG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℚ[X]) P
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℚ[X]) P, b, hb0, ?_⟩
    have hof := coordToX0_C_ne_zero h hb0
    rw [coordToX0_C] at hof
    rw [coordToX0_C, eq_div_iff hof, coordToX0_mk, hG, Algebra.smul_def, map_mul, mul_comm]
    congr 1

/-- $\mathbb Q(X)[Y]/(F_N)$ is the field of fractions of $\mathbb Q[X, Y]/(F_N)$. -/
theorem isFractionRing_coordToX0 (h : Prop2_4 N) [NeZero N] :
    letI : Algebra (coordRing h) (X0Field h) := RingHom.toAlgebra (R := coordRing h) (S := X0Field h) (coordToX0 h)
    IsFractionRing (coordRing h) (X0Field h) := by
  letI : Algebra (coordRing h) (X0Field h) := RingHom.toAlgebra (R := coordRing h) (S := X0Field h) (coordToX0 h)
  haveI : FaithfulSMul (coordRing h) (X0Field h) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (coordToX0_injective h)
  refine IsFractionRing.of_field (R := coordRing h) (K := X0Field h) fun z => ?_
  obtain ⟨G, d, -, hz⟩ := exists_eq_div h z
  exact ⟨_, _, hz⟩

/-- **The function field of the plane model** (Milne V §2, pdf p. 195): `X0Field h` is isomorphic to the field of
fractions of the coordinate ring $\mathbb Q[X, Y]/(F_N)$. -/
@[kb "milne2006ec" "Ch. V, §2, Q(X_0(N)) is the field of fractions of Q[X,Y]/(F_N), pdf p. 195"]
noncomputable def x0FieldEquivFractionRing (h : Prop2_4 N) [NeZero N] :
    X0Field h ≃+* FractionRing (coordRing h) :=
  let _ : Algebra (coordRing h) (X0Field h) := RingHom.toAlgebra (R := coordRing h) (S := X0Field h) (coordToX0 h)
  have := isFractionRing_coordToX0 h
  (IsLocalization.algEquiv (R := coordRing h) (nonZeroDivisors (coordRing h)) (X0Field h)
    (FractionRing (coordRing h))).toRingEquiv

/-! ### The exact constant field -/

/-- **$\mathbb Q$ is algebraically closed in $\mathbb Q(X_0(N))$** (Milne V §2, pdf p. 195: $X_0(N)$ is a curve
over $\mathbb Q$): an element of `X0Field h` algebraic over $\mathbb Q$ is rational. -/
@[kb "milne2006ec" "Ch. V, §2, Q is algebraically closed in Q(X_0(N)), pdf p. 195"]
theorem X0Field.eq_algebraMap_of_isAlgebraic (h : Prop2_4 N) [NeZero N] (z : X0Field h)
    (hz : IsAlgebraic ℚ z) : ∃ q : ℚ, z = algebraMap ℚ (X0Field h) q := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨G, d, hd, rfl⟩ := exists_eq_div h z
  obtain ⟨p, hp, hpz⟩ := hz
  set φ := coordToX0 h
  set a := Ideal.Quotient.mk (Ideal.span {modPolyQ h}) G
  set b := Ideal.Quotient.mk (Ideal.span {modPolyQ h}) (C d)
  have hb : φ b ≠ 0 := coordToX0_C_ne_zero h hd
  have hb' : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
  -- the image of `C d` under evaluation at `(j, j_N)` is nonzero
  have hQ : evalJJNRat N (C d) ≠ 0 := by
    intro h0
    apply hb'
    rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_evalJJNRat h, RingHom.mem_ker]
    exact h0
  -- clear denominators in `p (a / b) = 0`
  set cq : ℚ → coordRing h := fun q => Ideal.Quotient.mk (Ideal.span {modPolyQ h}) (C (C q)) with hcq
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      cq (p.coeff i) * (a ^ i * b ^ (p.natDegree - i)) = 0 := by
    apply coordToX0_injective h
    rw [map_zero, map_sum]
    have h1 := hpz
    rw [aeval_eq_sum_range] at h1
    have h2 := congrArg (fun x => x * φ b ^ p.natDegree) h1
    simp only [zero_mul, Finset.sum_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_mul, map_mul, map_pow, map_pow, Algebra.smul_def, div_pow, mul_assoc]
    congr 1
    · exact coordToX0_CC h _
    · rw [show p.natDegree = i + (p.natDegree - i) by omega, pow_add]
      field_simp
      rw [Nat.add_sub_cancel_left]
  have hroot : ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i : ℂ) • (evalJJNRat N G ^ i * evalJJNRat N (C d) ^ (p.natDegree - i)) = 0 := by
    have := congrArg (fun x => (coordRingEquiv h x : ℍ → ℂ)) hsum
    simp only [map_sum, map_mul, map_pow, map_zero, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul,
      Subring.coe_pow, ZeroMemClass.coe_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cq, a, b, coordRingEquiv_mk]
    funext z
    simp [evalJJNHom, Pi.smul_apply, Pi.mul_apply]
  obtain ⟨q, hq⟩ := algebraic_eq_rat_smul h hN G (C d) hQ p hp hroot
  refine ⟨q, ?_⟩
  rw [div_eq_iff hb]
  have hker : G - C (C q) * C d ∈ RingHom.ker (evalJJNRat N) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hq]
    funext z
    simp [evalJJNHom]
  rw [ker_evalJJNRat h] at hker
  have hzero : a - Ideal.Quotient.mk _ (C (C q)) * b = 0 := by
    rw [← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hker
  have := congrArg φ hzero
  rw [map_sub, map_mul, map_zero, sub_eq_zero] at this
  rw [this, coordToX0_CC]

/-! ### The Fricke involution on the function field -/

/-- $w_N$ on the coordinate ring, as a ring automorphism (an involution, `frickeCoord_frickeCoord`). -/
noncomputable def frickeCoordEquiv (h : Prop2_4 N) (hN : 1 ≤ N) : coordRing h ≃+* coordRing h :=
  RingEquiv.ofRingHom (frickeCoord h hN) (frickeCoord h hN)
    (RingHom.ext fun x => frickeCoord_frickeCoord h hN x) (RingHom.ext fun x => frickeCoord_frickeCoord h hN x)

/-- **The Fricke involution $w_N$ of $\mathbb Q(X_0(N))$** (Milne V §2: $z \mapsto -1/Nz$ exchanges $j$ and
$j_N$): the field automorphism extending `frickeCoord`. -/
@[kb "milne2006ec" "Ch. V, §2, the involution w_N : j ↔ j_N of Q(X_0(N)) (running text), pdf p. 194"]
noncomputable def frickeX0 (h : Prop2_4 N) [NeZero N] : X0Field h ≃+* X0Field h :=
  let _ : Algebra (coordRing h) (X0Field h) := RingHom.toAlgebra (R := coordRing h) (S := X0Field h) (coordToX0 h)
  have := isFractionRing_coordToX0 h
  IsFractionRing.ringEquivOfRingEquiv (A := coordRing h) (B := coordRing h) (K := X0Field h) (L := X0Field h)
    (frickeCoordEquiv h (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))

theorem frickeX0_coordToX0 (h : Prop2_4 N) [NeZero N] (x : coordRing h) :
    frickeX0 h (coordToX0 h x) =
      coordToX0 h (frickeCoord h (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) x) := by
  let _ : Algebra (coordRing h) (X0Field h) := RingHom.toAlgebra (R := coordRing h) (S := X0Field h) (coordToX0 h)
  have := isFractionRing_coordToX0 h
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := coordRing h) (B := coordRing h) (K := X0Field h)
    (L := X0Field h) _ x

theorem frickeX0_frickeX0 (h : Prop2_4 N) [NeZero N] (z : X0Field h) : frickeX0 h (frickeX0 h z) = z := by
  obtain ⟨G, d, -, rfl⟩ := exists_eq_div h z
  simp only [map_div₀, frickeX0_coordToX0, frickeCoord_frickeCoord]

/-- The class of $X$ (the function $j$) in `X0Field h`. -/
noncomputable def jX0 (h : Prop2_4 N) : X0Field h := coordToX0 h (Ideal.Quotient.mk _ (C X))

/-- The class of $Y$ (the function $j_N$) in `X0Field h`. -/
noncomputable def jNX0 (h : Prop2_4 N) : X0Field h := coordToX0 h (Ideal.Quotient.mk _ X)

theorem frickeX0_jX0 (h : Prop2_4 N) [NeZero N] : frickeX0 h (jX0 h) = jNX0 h := by
  rw [jX0, frickeX0_coordToX0, frickeCoord_mk, swapQ_C_X]
  rfl

theorem frickeX0_jNX0 (h : Prop2_4 N) [NeZero N] : frickeX0 h (jNX0 h) = jX0 h := by
  rw [jNX0, frickeX0_coordToX0, frickeCoord_mk, swapQ_X]
  rfl

/-! ### Unconditional objects -/

/-- Proposition 2.4 for $N \ne 0$. -/
theorem prop2_4' (N : ℕ) [NeZero N] : Prop2_4 N := prop2_4 (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))

/-- The modular polynomial $F_N \in \mathbb Q[X][Y]$ (Milne V §2, Proposition 2.4). -/
noncomputable abbrev modPoly (N : ℕ) [NeZero N] : ℚ[X][X] := modPolyQ (prop2_4' N)

/-- The coordinate ring $\mathbb Q[X, Y]/(F_N)$ of the plane model of $X_0(N)$. -/
abbrev coordRingX0 (N : ℕ) [NeZero N] : Type := coordRing (prop2_4' N)

/-- The function field $\mathbb Q(X_0(N))$. -/
abbrev X0 (N : ℕ) [NeZero N] : Type := X0Field (prop2_4' N)

theorem modPoly_monic [NeZero N] : (modPoly N).Monic := modPolyQ_monic _

theorem modPoly_natDegree [NeZero N] : (modPoly N).natDegree = (CongruenceSubgroup.Gamma0 N).index :=
  modPolyQ_natDegree _

/-- $F_N$ generates the ideal of $(j, j_N)$ over $\mathbb Q$, for every $N \ge 1$. -/
theorem ker_evalJJNRat_modPoly [NeZero N] : RingHom.ker (evalJJNRat N) = Ideal.span {modPoly N} :=
  ker_evalJJNRat _

/-- $F_N$ is irreducible over $\mathbb Q$, for every $N \ge 1$. -/
theorem irreducible_modPoly [NeZero N] : Irreducible (modPoly N) :=
  irreducible_modPolyQ _ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))

/-- $F_N(X, Y) = F_N(Y, X)$ for $N > 1$. -/
theorem swapQ_modPoly [NeZero N] (hN : 1 < N) : swapQ (modPoly N) = modPoly N := swapQ_modPolyQ _ hN

/-- $[\mathbb Q(X_0(N)) : \mathbb Q(j)] = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$, for every $N \ge 1$. -/
theorem finrank_X0 [NeZero N] :
    Module.finrank (RatFunc ℚ) (X0 N) = (CongruenceSubgroup.Gamma0 N).index := finrank_X0Field _

/-- $\mathbb Q(X_0(N))$ is a function field in one variable over $\mathbb Q$, for every $N \ge 1$. -/
theorem functionField_X0 [NeZero N] : FunctionField ℚ (X0 N) := functionField_X0Field _

end NumberFieldKB.ModularCurves
