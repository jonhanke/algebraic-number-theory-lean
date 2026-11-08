import NumberFieldKB.MilneEC.Ch5JFunction

/-!
# The plane model $F_N(X, Y) = 0$ of $X_0(N)$ over $\mathbb Q$
J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 (pdf pp. 192–195). Milne defines $X_0(N)$ over
$\mathbb Q$ as the nonsingular projective curve attached to the plane curve $F_N(X, Y) = 0$, where $F_N$ is the modular
polynomial: the minimal polynomial of $j_N(z) = j(Nz)$ over $\mathbb C(j)$, which has rational coefficients
(Proposition 2.4, the named `Prop2_4`). A nonsingular projective curve is determined by its function field, so the
algebraic object to build first is the function field $\mathbb Q(X_0(N))$ of the plane curve, together with its
comparison with the analytic functions $j$, $j_N$ on $\mathbb H$.

This file proves, from the named `Prop2_4` (and `ModularPolynomial` for the complex version):

* `ker_evalJJNRat`: the polynomials $G \in \mathbb Q[X][Y]$ with $G(j, j_N) = 0$ on $\mathbb H$ are exactly the
  multiples of $F_N$; hence `coordRingEquiv`: the coordinate ring $\mathbb Q[X, Y]/(F_N)$ of the plane curve is
  isomorphic to the ring $\mathbb Q[j, j_N]$ of functions on $\mathbb H$ (the analytic comparison for the affine model).
* `mdiff_mul_eq_zero`: holomorphic functions on $\mathbb H$ have no zero divisors (identity theorem).
* `irreducible_modPolyQ`, `irreducible_modPolyC`: $F_N$ is irreducible in $\mathbb Q[X][Y]$ and in
  $\mathbb C[X][Y]$ (the plane curve is geometrically irreducible), and `irreducible_modPolyQ_map`: irreducible over
  $\mathbb Q(X)$.
* `X0Field`: the function field $\mathbb Q(X_0(N)) = \mathbb Q(X)[Y]/(F_N)$, a field, a function field in one variable
  over $\mathbb Q$ (`functionField_X0Field`) of degree $(\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$ over
  $\mathbb Q(X) = \mathbb Q(j)$ (`finrank_X0Field`).

The plane curve is the field `X0Field` read through its generators $X \mapsto j$, $Y \mapsto j_N$; the nonsingular
projective model (its places) and the identification of `X0Field ⊗ ℂ` with the meromorphic functions on
$\Gamma_0(N)\backslash\mathbb H^*$ (Theorem 2.3, the named `Thm2_3`) are later milestones of the plan.
-/

open UpperHalfPlane hiding I
open Polynomial
open scoped Manifold

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ)

/-! ### Evaluation at $(j, j_N)$ -/

/-- Evaluation of $G(X, Y) \in R[X][Y]$ at $(j(z), j_N(z))$, as a ring homomorphism to functions on $\mathbb H$, for a
ring homomorphism $\iota : R \to \mathbb C$ applied to the coefficients. -/
noncomputable def evalJJNHom {R : Type*} [CommRing R] (ι : R →+* ℂ) : R[X][X] →+* (ℍ → ℂ) :=
  eval₂RingHom (eval₂RingHom ((Pi.constRingHom ℍ ℂ).comp ι) jFun) (jN N)

theorem evalJJNHom_apply {R : Type*} [CommRing R] (ι : R →+* ℂ) (G : R[X][X]) (z : ℍ) :
    evalJJNHom N ι G z = evalJJN N (G.map (mapRingHom ι)) z := by
  have key : (Pi.evalRingHom (fun _ : ℍ => ℂ) z).comp (evalJJNHom N ι) =
      (evalRingHom (jN N z)).comp ((mapRingHom (evalRingHom (jFun z))).comp (mapRingHom (mapRingHom ι))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp [evalJJNHom]
      · simp [evalJJNHom]
    · simp [evalJJNHom]
  have := RingHom.congr_fun key G
  simpa [evalJJN, Polynomial.map_map] using this

/-- The evaluation homomorphism with rational coefficients. -/
noncomputable abbrev evalJJNRat : ℚ[X][X] →+* (ℍ → ℂ) := evalJJNHom N (algebraMap ℚ ℂ)

/-- The evaluation homomorphism with complex coefficients. -/
noncomputable abbrev evalJJNC : ℂ[X][X] →+* (ℍ → ℂ) := evalJJNHom N (RingHom.id ℂ)

/-! ### The modular polynomial -/

variable {N}

/-- The modular polynomial $F_N \in \mathbb Q[X][Y]$ given by the named Proposition 2.4. -/
noncomputable def modPolyQ (h : Prop2_4 N) : ℚ[X][X] := h.exists_poly.choose

/-- The modular polynomial $F_N \in \mathbb C[X][Y]$ given by the named `ModularPolynomial`. -/
noncomputable def modPolyC (h : ModularPolynomial N) : ℂ[X][X] := h.exists_poly.choose

theorem modPolyQ_monic (h : Prop2_4 N) : (modPolyQ h).Monic := h.exists_poly.choose_spec.1

theorem modPolyQ_natDegree (h : Prop2_4 N) :
    (modPolyQ h).natDegree = (CongruenceSubgroup.Gamma0 N).index := h.exists_poly.choose_spec.2.1

theorem modPolyC_monic (h : ModularPolynomial N) : (modPolyC h).Monic := h.exists_poly.choose_spec.1

private theorem injective_mapRingHom_rat :
    Function.Injective (mapRingHom (algebraMap ℚ ℂ) : ℚ[X] →+* ℂ[X]) := by
  rw [coe_mapRingHom]
  exact map_injective _ (algebraMap ℚ ℂ).injective

/-- **The ideal of the plane model** (Milne V §2, pdf p. 193): a polynomial $G \in \mathbb Q[X][Y]$ vanishes at
$(j(z), j(Nz))$ for every $z \in \mathbb H$ iff $F_N$ divides $G$. -/
@[kb "milne2006ec" "Ch. V, §2, F_N generates the ideal of (j, j_N) over Q (Prop. 2.4 and its proof), pdf p. 193"]
theorem ker_evalJJNRat (h : Prop2_4 N) : RingHom.ker (evalJJNRat N) = Ideal.span {modPolyQ h} := by
  obtain ⟨hm, -, hzero, hdiv⟩ := h.exists_poly.choose_spec
  ext G
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hG
    have h0 : ∀ z, evalJJN N (G.map (mapRingHom (algebraMap ℚ ℂ))) z = 0 := fun z => by
      rw [← evalJJNHom_apply, hG]; rfl
    have hd := hdiv _ h0
    show h.exists_poly.choose ∣ G
    rw [← modByMonic_eq_zero_iff_dvd hm]
    apply map_injective _ injective_mapRingHom_rat
    rw [map_modByMonic _ hm, Polynomial.map_zero]
    exact (modByMonic_eq_zero_iff_dvd (hm.map _)).2 hd
  · rintro ⟨H, rfl⟩
    rw [map_mul]
    funext z
    simp only [Pi.mul_apply, Pi.zero_apply, evalJJNHom_apply]
    rw [show evalJJN N ((modPolyQ h).map (mapRingHom (algebraMap ℚ ℂ))) z = 0 from hzero z, zero_mul]

/-- The complex version of `ker_evalJJNRat`, from the named `ModularPolynomial`. -/
@[kb "milne2006ec" "Ch. V, §2, F_N generates the ideal of (j, j_N) over C, pdf p. 193"]
theorem ker_evalJJNC (h : ModularPolynomial N) : RingHom.ker (evalJJNC N) = Ideal.span {modPolyC h} := by
  obtain ⟨hm, -, hzero, hdiv⟩ := h.exists_poly.choose_spec
  have hmap : ∀ G : ℂ[X][X], G.map (mapRingHom (RingHom.id ℂ)) = G := fun G => by
    rw [mapRingHom_id]; exact Polynomial.map_id
  ext G
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hG
    refine hdiv _ fun z => ?_
    rw [← hmap G, ← evalJJNHom_apply, hG]; rfl
  · rintro ⟨H, rfl⟩
    rw [map_mul]
    funext z
    simp only [Pi.mul_apply, Pi.zero_apply, evalJJNHom_apply, hmap]
    rw [show evalJJN N (modPolyC h) z = 0 from hzero z, zero_mul]

/-! ### Holomorphic functions on $\mathbb H$ have no zero divisors -/

/-- **Identity theorem on $\mathbb H$**: if $f g = 0$ for holomorphic $f, g$ on $\mathbb H$, then $f = 0$ or $g = 0$. -/
theorem mdiff_mul_eq_zero {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) (hfg : f * g = 0) :
    f = 0 ∨ g = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hf0, hg0⟩ := hcon
  apply hg0
  obtain ⟨z0, hz0⟩ : ∃ z, f z ≠ 0 := by
    by_contra! H
    exact hf0 (funext H)
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have hFa : AnalyticOnNhd ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hf).analyticOnNhd hU
  have hGa : AnalyticOnNhd ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hg).analyticOnNhd hU
  have hz0U : (z0 : ℂ) ∈ {z : ℂ | 0 < z.im} := z0.im_pos
  have hev : ∀ᶠ w in nhds (z0 : ℂ), (f ∘ ofComplex) w ≠ 0 :=
    (hFa _ hz0U).continuousAt.eventually_ne (by simpa [ofComplex_apply] using hz0)
  have hG0 : (g ∘ ofComplex) =ᶠ[nhds (z0 : ℂ)] 0 := by
    filter_upwards [hev] with w hw
    have := congrFun hfg (ofComplex w)
    simp only [Pi.mul_apply, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hw
  have heq := hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hz0U hG0
  funext z
  simpa [ofComplex_apply] using heq z.im_pos

/-- Every $G(j, j_N)$ is holomorphic on $\mathbb H$. -/
theorem mdifferentiable_evalJJNHom {R : Type*} [CommRing R] (ι : R →+* ℂ) (hN : 1 ≤ N) (G : R[X][X]) :
    MDiff (evalJJNHom N ι G) := by
  have hc : ∀ a : R[X], MDiff (eval₂RingHom ((Pi.constRingHom ℍ ℂ).comp ι) jFun a) := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | monomial n c =>
      simp only [coe_eval₂RingHom, eval₂_monomial]
      exact mdifferentiable_const.mul (jFun_mdifferentiable.pow n)
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    simp only [evalJJNHom, coe_eval₂RingHom, eval₂_monomial]
    exact (hc a).mul ((jN_mdifferentiable hN).pow n)

/-- The kernel of an evaluation at $(j, j_N)$ is a prime ideal. -/
theorem isPrime_ker_evalJJNHom {R : Type*} [CommRing R] (ι : R →+* ℂ) (hN : 1 ≤ N) :
    (RingHom.ker (evalJJNHom N ι)).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    intro h1
    have := congrFun h1 UpperHalfPlane.I
    simp at this
  · rw [RingHom.mem_ker, map_mul] at hab
    rcases mdiff_mul_eq_zero (mdifferentiable_evalJJNHom ι hN a)
      (mdifferentiable_evalJJNHom ι hN b) hab with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **$F_N$ is irreducible over $\mathbb Q$** (Milne V §2, pdf p. 193: $F_N(j, Y)$ is the minimal polynomial of $j_N$
over $\mathbb C(j)$, so $F_N(X, Y)$ is irreducible). -/
@[kb "milne2006ec" "Ch. V, §2, the modular polynomial is irreducible, pdf p. 193"]
theorem irreducible_modPolyQ (h : Prop2_4 N) (hN : 1 ≤ N) : Irreducible (modPolyQ h) := by
  have hp := isPrime_ker_evalJJNHom (N := N) (algebraMap ℚ ℂ) hN
  rw [ker_evalJJNRat h, Ideal.span_singleton_prime (modPolyQ_monic h).ne_zero] at hp
  exact hp.irreducible

/-- **$F_N$ is irreducible over $\mathbb C$**: the plane curve $F_N(X, Y) = 0$ is geometrically irreducible. -/
@[kb "milne2006ec" "Ch. V, §2, the curve F_N(X, Y) = 0 is irreducible over C, pdf pp. 193-194"]
theorem irreducible_modPolyC (h : ModularPolynomial N) (hN : 1 ≤ N) : Irreducible (modPolyC h) := by
  have hp := isPrime_ker_evalJJNHom (N := N) (RingHom.id ℂ) hN
  rw [ker_evalJJNC h, Ideal.span_singleton_prime (modPolyC_monic h).ne_zero] at hp
  exact hp.irreducible

/-! ### The coordinate ring and the function field -/

/-- The coordinate ring $\mathbb Q[X, Y]/(F_N)$ of the plane model of $X_0(N)$. -/
abbrev coordRing (h : Prop2_4 N) : Type := ℚ[X][X] ⧸ Ideal.span {modPolyQ h}

/-- **Analytic comparison for the affine model**: $\mathbb Q[X, Y]/(F_N) \cong \mathbb Q[j, j_N]$, the ring of
functions $z \mapsto G(j(z), j(Nz))$ on $\mathbb H$, by $X \mapsto j$, $Y \mapsto j_N$. -/
@[kb "milne2006ec" "Ch. V, §2, Q[X,Y]/(F_N) = Q[j, j_N], pdf pp. 193-195"]
noncomputable def coordRingEquiv (h : Prop2_4 N) : coordRing h ≃+* (evalJJNRat N).range :=
  (Ideal.quotEquivOfEq (ker_evalJJNRat h).symm).trans (RingHom.quotientKerEquivRange _)

theorem coordRingEquiv_mk (h : Prop2_4 N) (G : ℚ[X][X]) :
    (coordRingEquiv h (Ideal.Quotient.mk _ G) : ℍ → ℂ) = evalJJNRat N G := rfl

instance (h : Prop2_4 N) [NeZero N] : (Ideal.span {modPolyQ h}).IsPrime := by
  rw [← ker_evalJJNRat h]
  exact isPrime_ker_evalJJNHom _ (Nat.one_le_iff_ne_zero.2 (NeZero.ne N))

/-- The coordinate ring of the plane model is a domain. -/
example (h : Prop2_4 N) [NeZero N] : IsDomain (coordRing h) := inferInstance

/-- $F_N$ stays irreducible over $\mathbb Q(X)$ (Gauss's lemma; $F_N$ is monic). -/
theorem irreducible_modPolyQ_map (h : Prop2_4 N) [NeZero N] :
    Irreducible ((modPolyQ h).map (algebraMap ℚ[X] (RatFunc ℚ))) :=
  ((modPolyQ_monic h).irreducible_iff_irreducible_map_fraction_map).1
    (irreducible_modPolyQ h (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)))

/-- **The function field $\mathbb Q(X_0(N))$** (Milne V §2, pdf p. 195): $\mathbb Q(X)[Y]/(F_N(X, Y))$, the function
field of the plane curve $F_N = 0$ and so of its nonsingular projective model $X_0(N)$; $X$ is $j$, $Y$ is $j_N$. -/
@[kb "milne2006ec" "Ch. V, §2, the function field Q(j, j_N) of X_0(N) over Q, pdf p. 195"]
abbrev X0Field (h : Prop2_4 N) : Type := AdjoinRoot ((modPolyQ h).map (algebraMap ℚ[X] (RatFunc ℚ)))

instance (h : Prop2_4 N) [NeZero N] :
    Fact (Irreducible ((modPolyQ h).map (algebraMap ℚ[X] (RatFunc ℚ)))) :=
  ⟨irreducible_modPolyQ_map h⟩

noncomputable example (h : Prop2_4 N) [NeZero N] : Field (X0Field h) := inferInstance

/-- $[\mathbb Q(X_0(N)) : \mathbb Q(j)] = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$, the degree of $j : X_0(N) \to X_0(1)$. -/
@[kb "milne2006ec" "Ch. V, §2, degree of Q(j, j_N) over Q(j), pdf p. 193"]
theorem finrank_X0Field (h : Prop2_4 N) [NeZero N] :
    Module.finrank (RatFunc ℚ) (X0Field h) = (CongruenceSubgroup.Gamma0 N).index := by
  rw [(AdjoinRoot.powerBasis (irreducible_modPolyQ_map h).ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    ((modPolyQ_monic h)).natDegree_map, modPolyQ_natDegree]

/-- $\mathbb Q(X_0(N))$ is a function field in one variable over $\mathbb Q$ (finite over $\mathbb Q(X)$). -/
theorem functionField_X0Field (h : Prop2_4 N) [NeZero N] : FunctionField ℚ (X0Field h) :=
  (AdjoinRoot.powerBasis (irreducible_modPolyQ_map h).ne_zero).finite

end NumberFieldKB.ModularCurves
