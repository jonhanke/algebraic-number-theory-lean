import NumberFieldKB.ModularCurves.FrickeHecke
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The trace of $X_0(M) \to X_0(N)$ as a sum over cosets, and $T(p)$ as $\sum_\alpha f(\alpha z)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §4 (pdf p. 205): the Hecke operator acts on a function $f$ on
$X_0(N)$ by $f \mapsto \sum_\alpha f \circ \alpha$, $\alpha$ running over $\Gamma_0(N)\backslash\Gamma_0(N)
\begin{pmatrix}1&0\\0&p\end{pmatrix}\Gamma_0(N)$. Here `heckeOnFunctions` is defined algebraically, as
$\operatorname{Tr}_{\mathbb Q(X_0(pN))/\mathbb Q(X_0(N))} \circ \iota_p$. This file proves that the two agree.

* `holGerm`: the germs of holomorphic functions on $\mathbb H$ along the codiscrete filter, an integral domain;
  `FracHol` its field of fractions, `fracToGerm` the map back to germs.
* `sigmaG g`: for holomorphic $g$ with $F_M(j, g) = 0$, the embedding $\mathbb Q(X_0(M)) \to$ `FracHol` with
  $j \mapsto j$, $j_M \mapsto g$. For $\gamma \in \mathrm{SL}_2(\mathbb Z)$, `sigmaγ γ` takes $g = j_M \circ \gamma$:
  it is $x \mapsto x \circ \gamma$ (`fracToGerm_sigmaγ_x0Frac`).
* For $N \mid M$ and $\gamma \in \Gamma_0(N)$ these are embeddings over $\mathbb Q(X_0(N))$, depending only on the
  coset $\Gamma_0(M)\gamma$, and distinct cosets give distinct embeddings (`j_M` separates them,
  `mem_gamma0_of_jN_smul`). There are $(\Gamma_0(N):\Gamma_0(M)) = [\mathbb Q(X_0(M)):\mathbb Q(X_0(N))]$ cosets,
  so these are all the embeddings into an algebraic closure, and Mathlib's `trace_eq_sum_embeddings` gives
  **`toGerm_trace_x0Frac`**: $\operatorname{Tr}(f) = \sum_{\Gamma_0(M)\gamma} f \circ \gamma$ as functions on
  $\mathbb H$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex Topology
open scoped Manifold MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.V

/-! ### Holomorphic germs and their field of fractions -/

/-- The germs of holomorphic functions on $\mathbb H$, a subring of `HGerm`. -/
def holGerm : Subring HGerm where
  carrier := {x | ∃ g : ℍ → ℂ, MDiff g ∧ germ g = x}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, mdifferentiable_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, mdifferentiable_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- The germ of a holomorphic function, as an element of `holGerm`. -/
def hol (g : ℍ → ℂ) (hg : MDiff g) : holGerm := ⟨germ g, g, hg, rfl⟩

theorem hol_ne_zero {g : ℍ → ℂ} (hg : MDiff g) (h0 : g ≠ 0) : hol g hg ≠ 0 := fun h =>
  h0 ((germ_eq_zero_iff hg).1 (congrArg Subtype.val h))

instance : Nontrivial holGerm := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩

instance : NoZeroDivisors holGerm := by
  refine ⟨?_⟩
  rintro ⟨_, f, hf, rfl⟩ ⟨_, g, hg, rfl⟩ h
  have h' : germ (f * g) = 0 := congrArg Subtype.val h
  rcases mdiff_mul_eq_zero hf hg ((germ_eq_zero_iff (hf.mul hg)).1 h') with h0 | h0
  · left
    subst h0
    rfl
  · right
    subst h0
    rfl

instance : IsDomain holGerm := NoZeroDivisors.to_isDomain _

/-- The field of fractions of the holomorphic germs (meromorphic functions on $\mathbb H$). -/
abbrev FracHol : Type := FractionRing holGerm

theorem isUnit_of_ne_zero_holGerm (y : holGerm) (hy : y ≠ 0) : IsUnit (y : HGerm) := by
  obtain ⟨_, g, hg, rfl⟩ := y
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hy rfl
  exact isUnit_germ hg hg0

/-- `FracHol` $\to$ germs. -/
noncomputable def fracToGerm : FracHol →+* HGerm :=
  IsLocalization.lift (M := nonZeroDivisors holGerm) (g := holGerm.subtype)
    fun y => isUnit_of_ne_zero_holGerm y (nonZeroDivisors.ne_zero y.2)

theorem fracToGerm_algebraMap (x : holGerm) : fracToGerm (algebraMap holGerm FracHol x) = x :=
  IsLocalization.lift_eq _ _

theorem fracToGerm_injective : Function.Injective fracToGerm := fracToGerm.injective

/-- $\mathbb Q[X] \to$ holomorphic germs, $X \mapsto j$. -/
noncomputable def polyToHol : ℚ[X] →+* holGerm :=
  polyToGerm.codRestrict holGerm fun p => ⟨_, fun z => mdiffAt_eval_jFun (p.map (algebraMap ℚ ℂ)) z, (polyToGerm_apply p).symm⟩

theorem polyToHol_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : polyToHol p ≠ 0 := fun h =>
  (isUnit_polyToGerm hp).ne_zero (congrArg Subtype.val h)

/-- $\mathbb Q(X) \to$ `FracHol`, $X \mapsto j$. -/
noncomputable def ratToFrac : RatFunc ℚ →+* FracHol :=
  IsLocalization.lift (M := nonZeroDivisors ℚ[X]) (S := RatFunc ℚ)
    (g := (algebraMap holGerm FracHol).comp polyToHol) fun y => by
      refine IsUnit.mk0 _ ?_
      rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
      exact polyToHol_ne_zero (nonZeroDivisors.ne_zero y.2)

theorem ratToFrac_comp : ratToFrac.comp (algebraMap ℚ[X] (RatFunc ℚ)) = (algebraMap holGerm FracHol).comp polyToHol :=
  RingHom.ext fun p => IsLocalization.lift_eq _ p

/-! ### Evaluation at $(j, g)$ -/

/-- $G \mapsto (z \mapsto G(j(z), g(z)))$. -/
noncomputable def evalJG (g : ℍ → ℂ) : ℚ[X][X] →+* (ℍ → ℂ) :=
  eval₂RingHom (eval₂RingHom ((Pi.constRingHom ℍ ℂ).comp (algebraMap ℚ ℂ)) jFun) g

theorem evalJG_jN (M : ℕ) : evalJG (jN M) = evalJJNRat M := rfl

/-- Evaluation at $(j, g)$ in the holomorphic germs. -/
noncomputable def holEval (g : ℍ → ℂ) (hg : MDiff g) : ℚ[X][X] →+* holGerm := eval₂RingHom polyToHol (hol g hg)

theorem holEval_val {g : ℍ → ℂ} (hg : MDiff g) (G : ℚ[X][X]) :
    (holEval g hg G : HGerm) = germ (evalJG g G) := by
  have key : holGerm.subtype.comp (holEval g hg) = (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (evalJG g) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · exact RingHom.ext_rat _ _
      · show ((holEval g hg (C X) : holGerm) : HGerm) = germ (evalJG g (C X))
        rw [show holEval g hg (C X) = polyToHol X from eval₂_C _ _]
        change polyToGerm X = _
        rw [polyToGerm_apply]
        congr 1
        funext z
        simp [evalJG]
    · show ((holEval g hg X : holGerm) : HGerm) = germ (evalJG g X)
      rw [show holEval g hg X = hol g hg from eval₂_X _ _]
      change germ g = _
      congr 1
      funext z
      simp [evalJG]
  exact RingHom.congr_fun key G

theorem mdiff_evalJG {g : ℍ → ℂ} (hg : MDiff g) (G : ℚ[X][X]) : MDiff (evalJG g G) := by
  have hc : ∀ a : ℚ[X], MDiff (eval₂RingHom ((Pi.constRingHom ℍ ℂ).comp (algebraMap ℚ ℂ)) jFun a) := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | monomial n c =>
      simp only [coe_eval₂RingHom, eval₂_monomial]
      exact mdifferentiable_const.mul (jFun_mdifferentiable.pow n)
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    simp only [evalJG, coe_eval₂RingHom, eval₂_monomial]
    exact (hc a).mul (hg.pow n)

/-! ### The embeddings $\sigma_g$ -/

variable {M : ℕ} [NeZero M]

/-- **The embedding with $j \mapsto j$, $j_M \mapsto g$**, for holomorphic $g$ with $F_M(j, g) = 0$. -/
noncomputable def sigmaG (g : ℍ → ℂ) (hg : MDiff g) (hF : evalJG g (modPoly M) = 0) : X0 M →+* FracHol :=
  AdjoinRoot.lift ratToFrac (algebraMap holGerm FracHol (hol g hg)) (by
    rw [eval₂_map, ratToFrac_comp, ← Polynomial.hom_eval₂]
    have : (modPolyQ (prop2_4' M)).eval₂ polyToHol (hol g hg) = 0 := by
      apply Subtype.ext
      change (holEval g hg (modPoly M) : HGerm) = 0
      rw [holEval_val, hF]
      rfl
    rw [this, map_zero])

theorem sigmaG_coordToX0 {g : ℍ → ℂ} (hg : MDiff g) (hF : evalJG g (modPoly M) = 0) (G : ℚ[X][X]) :
    sigmaG g hg hF (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ G)) =
      algebraMap holGerm FracHol (holEval g hg G) := by
  rw [coordToX0_mk, sigmaG, AdjoinRoot.lift_mk, eval₂_map, ratToFrac_comp, ← Polynomial.hom_eval₂]
  rfl

/-- If $f\,Q(j, g) = P(j, g)$ with $Q(j, g) \ne 0$, then $\sigma_g(P(j,j_M)/Q(j,j_M))$ is the germ of $f$. -/
theorem fracToGerm_sigmaG_x0Frac {g : ℍ → ℂ} (hg : MDiff g) (hF : evalJG g (modPoly M) = 0) {P Q : ℚ[X][X]}
    {f : ℍ → ℂ} (hQ : evalJG g Q ≠ 0) (hf : ∀ z, f z * evalJG g Q z = evalJG g P z) :
    fracToGerm (sigmaG g hg hF (x0Frac M P Q)) = germ f := by
  have hQ0 : sigmaG g hg hF (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q)) ≠ 0 := by
    rw [sigmaG_coordToX0, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    intro h0
    have := congrArg Subtype.val h0
    rw [holEval_val] at this
    exact hQ ((germ_eq_zero_iff (mdiff_evalJG hg Q)).1 this)
  have hu : IsUnit (germ (evalJG g Q)) := isUnit_germ (mdiff_evalJG hg Q) hQ
  have hmul : sigmaG g hg hF (x0Frac M P Q) * sigmaG g hg hF (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ Q)) =
      sigmaG g hg hF (coordToX0 (prop2_4' M) (Ideal.Quotient.mk _ P)) := by
    rw [x0Frac, map_div₀, div_mul_cancel₀ _ hQ0]
  have h2 := congrArg fracToGerm hmul
  rw [map_mul, sigmaG_coordToX0, sigmaG_coordToX0, fracToGerm_algebraMap, fracToGerm_algebraMap, holEval_val,
    holEval_val] at h2
  have h3 : germ (evalJG g P) = germ f * germ (evalJG g Q) := by
    rw [← Filter.Germ.coe_mul]
    congr 1
    funext z
    exact (hf z).symm
  rw [h3] at h2
  exact hu.mul_left_inj.1 h2

theorem sigmaG_congr {g g' : ℍ → ℂ} (e : g = g') (hg : MDiff g) (hF : evalJG g (modPoly M) = 0) (hg' : MDiff g')
    (hF' : evalJG g' (modPoly M) = 0) : sigmaG g hg hF = sigmaG g' hg' hF' := by
  subst e
  rfl

/-! ### The translates $x \mapsto x \circ \gamma$ -/

theorem mdiff_smul_SL (γ : SL(2, ℤ)) : MDiff (fun z : ℍ => γ • z) := by
  have hdet : 0 < (γ : GL (Fin 2) ℝ).det.val := by simp
  exact mdifferentiable_smul hdet

/-- $j_M \circ \gamma$. -/
def jMγ (M : ℕ) (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => jN M (γ • z)

theorem mdiff_jMγ (γ : SL(2, ℤ)) : MDiff (jMγ M γ) :=
  (jN_mdifferentiable (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))).comp (mdiff_smul_SL γ)

omit [NeZero M] in
theorem evalJG_jMγ (γ : SL(2, ℤ)) (G : ℚ[X][X]) (z : ℍ) : evalJG (jMγ M γ) G z = evalJJNRat M G (γ • z) := by
  let c : (ℍ → ℂ) →+* (ℍ → ℂ) := RingHom.pi fun w => Pi.evalRingHom (fun _ : ℍ => ℂ) (γ • w)
  have key : evalJG (jMγ M γ) = c.comp (evalJJNRat M) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · exact RingHom.ext_rat _ _
      · show evalJG (jMγ M γ) (C X) = c (evalJJNRat M (C X))
        funext w
        show evalJG (jMγ M γ) (C X) w = evalJJNRat M (C X) (γ • w)
        simp only [evalJG, evalJJNHom, coe_eval₂RingHom, eval₂_C, eval₂_X]
        exact (V.jFun_smul γ w).symm
    · show evalJG (jMγ M γ) X = c (evalJJNRat M X)
      funext w
      show evalJG (jMγ M γ) X w = evalJJNRat M X (γ • w)
      simp only [evalJG, evalJJNHom, coe_eval₂RingHom, eval₂_X]
      rfl
  rw [key]
  rfl

theorem evalJG_jMγ_modPoly (γ : SL(2, ℤ)) : evalJG (jMγ M γ) (modPoly M) = 0 := by
  have h0 : evalJJNRat M (modPoly M) = 0 := by
    have : modPoly M ∈ RingHom.ker (evalJJNRat M) := by
      rw [ker_evalJJNRat_modPoly]; exact Ideal.mem_span_singleton_self _
    exact this
  funext z
  rw [evalJG_jMγ, h0]
  rfl

/-- **The translate by $\gamma$**: $\mathbb Q(X_0(M)) \to$ `FracHol`, $x \mapsto x \circ \gamma$. -/
def sigmaγ (γ : SL(2, ℤ)) : X0 M →+* FracHol := sigmaG (jMγ M γ) (mdiff_jMγ γ) (evalJG_jMγ_modPoly γ)

omit [NeZero M] in
theorem evalJG_jMγ_ne_zero (γ : SL(2, ℤ)) {Q : ℚ[X][X]} (hQ : evalJJNRat M Q ≠ 0) : evalJG (jMγ M γ) Q ≠ 0 := by
  intro h
  apply hQ
  funext w
  have := congrFun h (γ⁻¹ • w)
  rw [evalJG_jMγ, smul_inv_smul] at this
  exact this

/-- **$\sigma_\gamma$ is $x \mapsto x\circ\gamma$**: if $f\,Q(j, j_M) = P(j, j_M)$ with $Q(j, j_M) \ne 0$, the image of
$P(j, j_M)/Q(j, j_M)$ is the germ of $f \circ \gamma$. -/
theorem fracToGerm_sigmaγ_x0Frac (γ : SL(2, ℤ)) {P Q : ℚ[X][X]} {f : ℍ → ℂ} (hQ : evalJJNRat M Q ≠ 0)
    (hf : ∀ z, f z * evalJJNRat M Q z = evalJJNRat M P z) :
    fracToGerm (sigmaγ γ (x0Frac M P Q)) = germ (fun z => f (γ • z)) :=
  fracToGerm_sigmaG_x0Frac _ _ (evalJG_jMγ_ne_zero γ hQ) fun z => by
    rw [evalJG_jMγ, evalJG_jMγ]; exact hf (γ • z)

theorem fracToGerm_sigmaγ_jNElt (γ : SL(2, ℤ)) {d : ℕ} (hd : d ∣ M) :
    fracToGerm (sigmaγ γ (jNElt M d hd)) = germ (fun z => jN d (γ • z)) :=
  fracToGerm_sigmaγ_x0Frac γ (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.1
    (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.2

theorem sigmaγ_jX0 (γ : SL(2, ℤ)) : sigmaγ γ (jX0 (prop2_4' M)) = algebraMap holGerm FracHol (polyToHol X) := by
  rw [jX0, sigmaγ, sigmaG_coordToX0]
  congr 1
  exact eval₂_C _ _

theorem sigmaγ_jNX0 (γ : SL(2, ℤ)) :
    sigmaγ γ (jNX0 (prop2_4' M)) = algebraMap holGerm FracHol (hol (jMγ M γ) (mdiff_jMγ γ)) := by
  rw [jNX0, sigmaγ, sigmaG_coordToX0]
  congr 1
  exact eval₂_X _ _

theorem sigmaγ_eq_of_mem {γ δ : SL(2, ℤ)} (h : δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M) :
    sigmaγ (M := M) γ = sigmaγ δ := by
  refine sigmaG_congr ?_ _ _ _ _
  funext z
  have e : δ • z = (δ * γ⁻¹) • (γ • z) := by rw [mul_smul, inv_smul_smul]
  simp only [jMγ]
  rw [e, jN_smul (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) h]

theorem mem_of_sigmaγ_jNX0_eq {γ δ : SL(2, ℤ)} (h : sigmaγ (M := M) γ (jNX0 (prop2_4' M)) = sigmaγ δ (jNX0 (prop2_4' M))) :
    δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M := by
  rw [sigmaγ_jNX0, sigmaγ_jNX0] at h
  have h1 := congrArg Subtype.val (IsFractionRing.injective holGerm FracHol h)
  change germ (jMγ M γ) = germ (jMγ M δ) at h1
  have h2 : jMγ M γ - jMγ M δ = 0 := by
    rw [← germ_eq_zero_iff ((mdiff_jMγ γ).sub (mdiff_jMγ δ))]
    change germ (jMγ M γ) - germ (jMγ M δ) = 0
    rw [h1, sub_self]
  refine mem_gamma0_of_jN_smul (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) fun w => ?_
  have := congrFun h2 (γ⁻¹ • w)
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, jMγ, smul_inv_smul] at this
  rw [mul_smul, ← this]

/-! ### Embeddings over $\mathbb Q(X_0(N))$ and the trace -/

section Trace

variable {N : ℕ} [NeZero N] (h : 1 * N ∣ M)

/-- The embedding $\mathbb Q(X_0(N)) \to$ `FracHol` through $z \mapsto z$, $X_0(M) \to X_0(N)$. -/
def baseHom : X0 N →+* FracHol := (sigmaγ (M := M) 1).comp (degeneracy N M 1 h)

/-- For $\gamma \in \Gamma_0(N)$, $\sigma_\gamma$ is an embedding over $\mathbb Q(X_0(N))$. -/
theorem sigmaγ_comp_degeneracy {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (sigmaγ γ).comp (degeneracy N M 1 h) = baseHom h := by
  apply X0.ringHom_ext
  · rw [baseHom, RingHom.comp_apply, RingHom.comp_apply, degeneracy_jX0, jNElt_one, sigmaγ_jX0, sigmaγ_jX0]
  · apply fracToGerm_injective
    rw [baseHom, RingHom.comp_apply, RingHom.comp_apply, degeneracy_jNX0, fracToGerm_sigmaγ_jNElt,
      fracToGerm_sigmaγ_jNElt]
    congr 1
    funext z
    rw [one_smul]
    exact jN_smul (by rw [one_mul]; exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (by rwa [one_mul]) z

/-- The right cosets $\Gamma_0(M)\gamma$ in $\Gamma_0(N)$. -/
abbrev CosetsNM (N M : ℕ) : Type :=
  Quotient (QuotientGroup.rightRel ((CongruenceSubgroup.Gamma0 M).subgroupOf (CongruenceSubgroup.Gamma0 N)))

instance : Finite (CosetsNM N M) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel _).symm

instance : Fintype (CosetsNM N M) := Fintype.ofFinite _

omit [NeZero M] [NeZero N] in
theorem natCard_cosetsNM : Nat.card (CosetsNM N M) =
    (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) := by
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]

/-- An algebraic closure of `FracHol`. -/
abbrev EClos : Type := AlgebraicClosure FracHol

/-- `EClos` over $\mathbb Q(X_0(N))$ through `baseHom`. -/
abbrev baseAlgebra : Algebra (X0 N) EClos := ((algebraMap FracHol EClos).comp (baseHom h)).toAlgebra

/-- $\sigma_\gamma$, $\gamma \in \Gamma_0(N)$, as an embedding of $\mathbb Q(X_0(M))$ over $\mathbb Q(X_0(N))$. -/
def embγ (γ : CongruenceSubgroup.Gamma0 N) :
    letI := forgetAlgebra N M h
    letI := baseAlgebra h
    X0 M →ₐ[X0 N] EClos :=
  letI := forgetAlgebra N M h
  letI := baseAlgebra h
  { (algebraMap FracHol EClos).comp (sigmaγ (γ : SL(2, ℤ))) with
    commutes' := fun x => by
      change algebraMap FracHol EClos (sigmaγ (γ : SL(2, ℤ)) (degeneracy N M 1 h x)) =
        algebraMap FracHol EClos (baseHom h x)
      rw [← sigmaγ_comp_degeneracy h γ.2]
      rfl }

theorem embγ_apply (γ : CongruenceSubgroup.Gamma0 N) (x : X0 M) :
    embγ h γ x = algebraMap FracHol EClos (sigmaγ (γ : SL(2, ℤ)) x) := rfl

/-- The embedding attached to a coset. -/
def embQ :
    letI := forgetAlgebra N M h
    letI := baseAlgebra h
    CosetsNM N M → (X0 M →ₐ[X0 N] EClos) :=
  letI := forgetAlgebra N M h
  letI := baseAlgebra h
  Quotient.lift (embγ h) fun a b hab => by
    have hab' : (b : SL(2, ℤ)) * (a : SL(2, ℤ))⁻¹ ∈ CongruenceSubgroup.Gamma0 M := by
      have := (QuotientGroup.rightRel_apply).1 hab
      rwa [Subgroup.mem_subgroupOf] at this
    ext x
    rw [embγ_apply, embγ_apply, sigmaγ_eq_of_mem hab']

theorem embQ_mk (γ : CongruenceSubgroup.Gamma0 N) : embQ h (Quotient.mk _ γ) = embγ h γ := rfl

theorem embQ_injective : Function.Injective (embQ h) := by
  intro c d hcd
  induction c using Quotient.inductionOn with
  | h a =>
  induction d using Quotient.inductionOn with
  | h b =>
  apply Quotient.sound
  have := congrArg (fun φ => φ (jNX0 (prop2_4' M))) hcd
  simp only [embQ_mk, embγ_apply] at this
  have h2 := mem_of_sigmaγ_jNX0_eq ((algebraMap FracHol EClos).injective this)
  refine (QuotientGroup.rightRel_apply).2 ?_
  rw [Subgroup.mem_subgroupOf]
  exact h2

theorem embQ_bijective : Function.Bijective (embQ h) := by
  let := forgetAlgebra N M h
  let := baseAlgebra h
  have := finite_forget (N := N) (M := M) h
  refine (embQ_injective h).bijective_of_nat_card_le ?_
  rw [natCard_cosetsNM, ← finrank_forget h, Nat.card_eq_fintype_card, AlgHom.card]

/-- **The trace as a sum over cosets**, in `FracHol`: $\operatorname{Tr}(x) = \sum_{\Gamma_0(M)\gamma} x\circ\gamma$. -/
theorem baseHom_trace (x : X0 M) :
    letI := forgetAlgebra N M h
    baseHom h (Algebra.trace (X0 N) (X0 M) x) =
      ∑ c : CosetsNM N M, sigmaγ ((Quotient.out c : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) x := by
  let := forgetAlgebra N M h
  let := baseAlgebra h
  have := finite_forget (N := N) (M := M) h
  apply (algebraMap FracHol EClos).injective
  have h1 := trace_eq_sum_embeddings EClos (K := X0 N) (L := X0 M) (x := x)
  change algebraMap FracHol EClos (baseHom h _) = _ at h1
  rw [h1, map_sum, ← Fintype.sum_bijective (embQ h) (embQ_bijective h) (fun c => embQ h c x) (fun σ => σ x)
    (fun _ => rfl)]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- `baseHom` followed by `fracToGerm` is `toGerm N`. -/
theorem fracToGerm_baseHom : fracToGerm.comp (baseHom h) = toGerm N := by
  apply X0.ringHom_ext
  · rw [RingHom.comp_apply, baseHom, RingHom.comp_apply, degeneracy_jX0, jNElt_one, ← jNElt_one (M := M) (one_dvd M),
      fracToGerm_sigmaγ_jNElt, toGerm_jX0]
    congr 1
    funext z
    rw [one_smul]
    unfold jN
    congr 1
    ext
    rw [coe_ofComplex_mul le_rfl]
    simp
  · rw [RingHom.comp_apply, baseHom, RingHom.comp_apply, degeneracy_jNX0, fracToGerm_sigmaγ_jNElt, toGerm_jNX0]
    congr 1
    funext z
    rw [one_smul, one_mul]

/-- **The trace of $X_0(M) \to X_0(N)$ is the sum over the cosets $\Gamma_0(M)\gamma \subset \Gamma_0(N)$** (Milne V §4):
if $f\,Q(j, j_M) = P(j, j_M)$ on $\mathbb H$ with $Q(j, j_M) \ne 0$, then the function of
$\operatorname{Tr}(P(j, j_M)/Q(j, j_M))$ is $z \mapsto \sum_{\Gamma_0(M)\gamma} f(\gamma z)$ (off a discrete set). -/
@[kb "milne2006ec" "Ch. V, §4, T(p) on functions: f ↦ Σ f(α z) over the cosets (running text), pdf p. 205"]
theorem toGerm_trace_x0Frac {P Q : ℚ[X][X]} {f : ℍ → ℂ} (hQ : evalJJNRat M Q ≠ 0)
    (hf : ∀ z, f z * evalJJNRat M Q z = evalJJNRat M P z) :
    letI := forgetAlgebra N M h
    toGerm N (Algebra.trace (X0 N) (X0 M) (x0Frac M P Q)) =
      ∑ c : CosetsNM N M, germ (fun z => f (((Quotient.out c : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z)) := by
  let := forgetAlgebra N M h
  rw [← fracToGerm_baseHom h, RingHom.comp_apply, baseHom_trace, map_sum]
  exact Finset.sum_congr rfl fun c _ => fracToGerm_sigmaγ_x0Frac _ hQ hf

end Trace

/-! ### $T(p)$ on functions is $f \mapsto \sum_\gamma f(p\gamma z)$ -/

section HeckeFunctions

variable {N : ℕ} [NeZero N]

theorem coordToX0_eq_eval₂ (G : ℚ[X][X]) :
    coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ G) =
      G.eval₂ (aeval (jX0 (prop2_4' N))).toRingHom (jNX0 (prop2_4' N)) := by
  have key : (coordToX0 (prop2_4' N)).comp (Ideal.Quotient.mk _) =
      eval₂RingHom (aeval (jX0 (prop2_4' N))).toRingHom (jNX0 (prop2_4' N)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · exact RingHom.ext_rat _ _
      · simp [jX0]
    · simp [jNX0]
  exact RingHom.congr_fun key G

/-- $G(x, y)$ under any ring map to germs, for $x \mapsto f_x$, $y \mapsto f_y$. -/
theorem ringHom_eval₂_aeval (ψ : X0 N →+* HGerm) {x y : X0 N} {fx fy : ℍ → ℂ} (hx : ψ x = germ fx)
    (hy : ψ y = germ fy) (G : ℚ[X][X]) :
    ψ (G.eval₂ (aeval x).toRingHom y) = germ (fun z =>
      ((G.map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (fx z))).eval (fy z)) := by
  have key : ψ.comp (eval₂RingHom (aeval x).toRingHom y) =
      (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
        (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (fx z)).comp
          (mapRingHom (algebraMap ℚ ℂ))))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat
          (((ψ.comp (eval₂RingHom (aeval x).toRingHom y)).comp C).comp C)
          ((((Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
            (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (fx z)).comp
              (mapRingHom (algebraMap ℚ ℂ)))))).comp C).comp C)
        exact RingHom.congr_fun this a
      · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, hx, Filter.Germ.coe_coeRingHom]
        congr 1
        funext z
        simp [RingHom.pi_apply]
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, hy, Filter.Germ.coe_coeRingHom]
      congr 1
      funext z
      simp [RingHom.pi_apply]
  have := RingHom.congr_fun key G
  rw [RingHom.comp_apply, coe_eval₂RingHom] at this
  rw [this, RingHom.comp_apply, Filter.Germ.coe_coeRingHom]
  congr 1
  funext z
  rw [RingHom.pi_apply, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, ← Polynomial.map_map]

omit [NeZero N] in
theorem jN_ofComplex_mul {p : ℕ} (hp : 1 ≤ p) (hN : 1 ≤ N) (u : ℍ) :
    jN N (ofComplex ((p : ℂ) * u)) = jN (p * N) u := by
  unfold jN
  congr 1
  ext
  rw [coe_ofComplex_mul hN, coe_ofComplex_mul hp, coe_ofComplex_mul (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega)))]
  push_cast
  ring

theorem evalJJNRat_ofComplex_mul {p : ℕ} (hp : 1 ≤ p) (G : ℚ[X][X]) (u : ℍ) :
    evalJJNRat N G (ofComplex ((p : ℂ) * u)) =
      ((G.map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jN p u))).eval (jN (p * N) u) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  rw [evalJJNHom_apply, evalJJN, jN_ofComplex_mul hp hN]
  rfl

variable (p : ℕ) [NeZero p]

/-- **$\sigma_\gamma \circ \iota_p$ is $f \mapsto f(p\gamma z)$**: if $f\,Q(j, j_N) = P(j, j_N)$ with $Q(j,j_N) \ne 0$,
the image of $\iota_p(P(j, j_N)/Q(j, j_N))$ under $\sigma_\gamma$ is the germ of $z \mapsto f(p\,\gamma z)$. -/
theorem fracToGerm_sigmaγ_degeneracy_x0Frac (γ : SL(2, ℤ)) {P Q : ℚ[X][X]} {f : ℍ → ℂ}
    (hQ : evalJJNRat N Q ≠ 0) (hf : ∀ z, f z * evalJJNRat N Q z = evalJJNRat N P z) :
    fracToGerm (sigmaγ (M := p * N) γ (degeneracy N (p * N) p dvd_rfl (x0Frac N P Q))) =
      germ (fun z => f (ofComplex ((p : ℂ) * ((γ • z : ℍ) : ℂ)))) := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  let τ : X0 N →+* FracHol := (sigmaγ (M := p * N) γ).comp (degeneracy N (p * N) p dvd_rfl)
  let ψ : X0 N →+* HGerm := fracToGerm.comp τ
  have hx : ψ (jX0 (prop2_4' N)) = germ (fun z => jN p (γ • z)) := by
    simp only [ψ, τ, RingHom.comp_apply, degeneracy_jX0, fracToGerm_sigmaγ_jNElt]
  have hy : ψ (jNX0 (prop2_4' N)) = germ (fun z => jN (p * N) (γ • z)) := by
    simp only [ψ, τ, RingHom.comp_apply, degeneracy_jNX0, fracToGerm_sigmaγ_jNElt]
  have hG : ∀ G : ℚ[X][X], ψ (coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ G)) =
      germ (fun z => evalJJNRat N G (ofComplex ((p : ℂ) * ((γ • z : ℍ) : ℂ)))) := by
    intro G
    rw [coordToX0_eq_eval₂, ringHom_eval₂_aeval ψ hx hy]
    congr 1
    funext z
    rw [evalJJNRat_ofComplex_mul hp]
  have hQ0 : coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q) ≠ 0 := by
    intro h0
    have := toGerm_coordToX0 (N := N) Q
    rw [h0, map_zero] at this
    exact hQ ((germ_eq_zero_iff (mdifferentiable_evalJJNHom _ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) Q)).1
      this.symm)
  have hu : IsUnit (ψ (coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q))) :=
    (IsUnit.mk0 _ ((map_ne_zero τ).2 hQ0)).map fracToGerm
  have hmul : x0Frac N P Q * coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q) =
      coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ P) := div_mul_cancel₀ _ hQ0
  have h2 := congrArg ψ hmul
  rw [map_mul, hG P] at h2
  have h3 : germ (fun z => evalJJNRat N P (ofComplex ((p : ℂ) * ((γ • z : ℍ) : ℂ)))) =
      germ (fun z => f (ofComplex ((p : ℂ) * ((γ • z : ℍ) : ℂ)))) * ψ (coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q)) := by
    rw [hG Q, ← Filter.Germ.coe_mul]
    congr 1
    funext z
    exact (hf _).symm
  rw [h3] at h2
  exact hu.mul_left_inj.1 h2

/-- **$T(p)$ on functions is Milne's $f \mapsto \sum_\alpha f \circ \alpha$** (Milne V §4): if $f\,Q(j, j_N) = P(j, j_N)$
on $\mathbb H$ with $Q(j, j_N) \ne 0$, the function of `heckeOnFunctions N p` applied to $P(j, j_N)/Q(j, j_N)$ is
$z \mapsto \sum_{\Gamma_0(pN)\gamma \subset \Gamma_0(N)} f(p\,\gamma z)$, i.e. $\sum_\alpha f(\alpha z)$ with
$\alpha = \begin{pmatrix}p&0\\0&1\end{pmatrix}\gamma$ (off a discrete set). -/
@[kb "milne2006ec" "Ch. V, §4, T(p) on functions: f ↦ Σ f(α z) over the cosets (running text), pdf p. 205"]
theorem toGerm_heckeOnFunctions_x0Frac {P Q : ℚ[X][X]} {f : ℍ → ℂ} (hQ : evalJJNRat N Q ≠ 0)
    (hf : ∀ z, f z * evalJJNRat N Q z = evalJJNRat N P z) :
    toGerm N (heckeOnFunctions N p (x0Frac N P Q)) =
      ∑ c : CosetsNM N (p * N), germ (fun z =>
        f (ofComplex ((p : ℂ) * ((((Quotient.out c : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z : ℍ) : ℂ)))) := by
  let := forgetAlgebra N (p * N) (one_mul_dvd_mul N p)
  have e : heckeOnFunctions N p (x0Frac N P Q) =
      Algebra.trace (X0 N) (X0 (p * N)) (degeneracy N (p * N) p dvd_rfl (x0Frac N P Q)) := rfl
  rw [e, ← fracToGerm_baseHom (one_mul_dvd_mul N p), RingHom.comp_apply, baseHom_trace, map_sum]
  exact Finset.sum_congr rfl fun c _ => fracToGerm_sigmaγ_degeneracy_x0Frac p _ hQ hf

end HeckeFunctions

end NumberFieldKB.ModularCurves

end
