import NumberFieldKB.ModularCurves.RationalFunctions
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# $\mathbb Q(X_0(N))$ as a field of meromorphic functions on $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 192–195). The analytic comparison for the
function field: `toGerm N` embeds $\mathbb Q(X_0(N)) = \mathbb Q(X)[Y]/(F_N)$ into the ring of germs of functions on
$\mathbb H$ along the codiscrete filter (functions up to equality off a discrete set), sending $X \mapsto j$,
$Y \mapsto j_N$. Its image is $\mathbb Q(j, j_N)$, a field of meromorphic functions; by Theorem 2.3 (`thm2_3`) its
$\mathbb C$-span of quotients is the field of all modular functions for $\Gamma_0(N)$.

Because `toGerm N` is injective (`toGerm_injective`), an identity in $\mathbb Q(X_0(N))$ can be checked on functions.
This is how the Hecke correspondences are built (`Hecke.lean`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex Topology
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- The codiscrete filter on $\mathbb H$ is proper. -/
instance neBot_codiscrete : (codiscrete ℍ).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have : ∀ᶠ _ in codiscrete ℍ, False := by rw [h]; exact Filter.eventually_bot
  have h2 := (eventually_codiscrete_iff_forall_eventually_nhdsNE.1 this) UpperHalfPlane.I
  exact h2.exists.elim fun _ h => h

/-- Germs of functions on $\mathbb H$ along the codiscrete filter. -/
noncomputable abbrev HGerm : Type := (codiscrete ℍ).Germ ℂ

/-- The germ of a function. -/
noncomputable abbrev germ (f : ℍ → ℂ) : HGerm := (f : HGerm)

theorem germ_eq_zero_iff {g : ℍ → ℂ} (hg : MDiff g) : germ g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have hev : ∀ᶠ z in codiscrete ℍ, g z = 0 := Filter.Germ.coe_eq.1 h
    have hfreq : ∃ᶠ z in 𝓝[≠] UpperHalfPlane.I, g z = 0 :=
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.1 hev) UpperHalfPlane.I).frequently
    exact UpperHalfPlane.eq_zero_of_frequently hg hfreq
  · rintro rfl
    rfl

theorem isUnit_germ {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0) : IsUnit (germ g) := by
  have h1 : germ g * germ (fun z => (g z)⁻¹) = 1 := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
    filter_upwards [eventually_codiscrete_ne_zero hg hg0] with z hz
    simp [hz]
  exact ⟨⟨germ g, germ (fun z => (g z)⁻¹), h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- $\mathbb Q[X] \to$ germs, $X \mapsto j$. -/
noncomputable def polyToGerm : ℚ[X] →+* HGerm :=
  (Filter.Germ.coeRingHom (codiscrete ℍ)).comp
    (RingHom.pi fun z => (evalRingHom (jFun z)).comp (mapRingHom (algebraMap ℚ ℂ)))

theorem polyToGerm_apply (p : ℚ[X]) :
    polyToGerm p = germ (fun z => (p.map (algebraMap ℚ ℂ)).eval (jFun z)) := rfl

theorem isUnit_polyToGerm {p : ℚ[X]} (hp : p ≠ 0) : IsUnit (polyToGerm p) := by
  rw [polyToGerm_apply]
  refine isUnit_germ (fun z => mdiffAt_eval_jFun _ z) fun h0 => hp ?_
  have hp' : p.map (algebraMap ℚ ℂ) = 0 := by
    refine Polynomial.funext fun t => ?_
    obtain ⟨w, rfl⟩ := jFun_surjective t
    simpa using congrFun h0 w
  exact (Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).1 hp'

/-- $\mathbb Q(X) \to$ germs, $X \mapsto j$. -/
noncomputable def ratFuncToGerm : RatFunc ℚ →+* HGerm :=
  IsLocalization.lift (M := nonZeroDivisors ℚ[X]) (S := RatFunc ℚ) (g := polyToGerm)
    fun y => isUnit_polyToGerm (nonZeroDivisors.ne_zero y.2)

theorem ratFuncToGerm_algebraMap (p : ℚ[X]) : ratFuncToGerm (algebraMap ℚ[X] (RatFunc ℚ) p) = polyToGerm p :=
  IsLocalization.lift_eq _ p

variable {N : ℕ}

/-- `X0Field h` $\to$ germs, $X \mapsto j$, $Y \mapsto j_N$. -/
noncomputable def toGermAux (h : Prop2_4 N) : X0Field h →+* HGerm :=
  AdjoinRoot.lift ratFuncToGerm (germ (jN N)) (by
    rw [eval₂_map]
    have hcomp : ratFuncToGerm.comp (algebraMap ℚ[X] (RatFunc ℚ)) = polyToGerm :=
      RingHom.ext ratFuncToGerm_algebraMap
    rw [hcomp]
    have key : (eval₂RingHom polyToGerm (germ (jN N))) =
        (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (evalJJNRat N) := by
      apply Polynomial.ringHom_ext'
      · apply Polynomial.ringHom_ext'
        · ext r
          simp [polyToGerm, evalJJNHom, RingHom.pi_apply]
          exact Filter.Eventually.of_forall fun z => by simp [RingHom.pi_apply]
        · simp [polyToGerm, evalJJNHom, RingHom.pi_apply]
          exact Filter.Eventually.of_forall fun z => by simp [RingHom.pi_apply]
      · simp [evalJJNHom]
    have := RingHom.congr_fun key (modPolyQ h)
    rw [coe_eval₂RingHom] at this
    rw [this, RingHom.comp_apply]
    have h0 : evalJJNRat N (modPolyQ h) = 0 := by
      funext z
      rw [evalJJNHom_apply]
      exact h.exists_poly.choose_spec.2.2.1 z
    rw [h0, map_zero])

theorem toGermAux_coordToX0 (h : Prop2_4 N) (G : ℚ[X][X]) :
    toGermAux h (coordToX0 h (Ideal.Quotient.mk _ G)) = germ (evalJJNRat N G) := by
  rw [coordToX0_mk, toGermAux, AdjoinRoot.lift_mk, eval₂_map]
  have hcomp : ratFuncToGerm.comp (algebraMap ℚ[X] (RatFunc ℚ)) = polyToGerm :=
    RingHom.ext ratFuncToGerm_algebraMap
  rw [hcomp]
  have key : (eval₂RingHom polyToGerm (germ (jN N))) =
      (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (evalJJNRat N) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp [polyToGerm, evalJJNHom, RingHom.pi_apply]
        exact Filter.Eventually.of_forall fun z => by simp [RingHom.pi_apply]
      · simp [polyToGerm, evalJJNHom, RingHom.pi_apply]
        exact Filter.Eventually.of_forall fun z => by simp [RingHom.pi_apply]
    · simp [evalJJNHom]
  have := RingHom.congr_fun key G
  rw [coe_eval₂RingHom] at this
  rw [this, RingHom.comp_apply, Filter.Germ.coe_coeRingHom]

/-- **The analytic comparison**:$\mathbb Q(X_0(N))$ embeds into the germs of functions on $\mathbb H$, with
$X \mapsto j$ and $Y \mapsto j_N$. -/
@[kb "milne2006ec" "Ch. V, §2, Q(X_0(N)) = Q(j, j_N) as a field of functions on ℍ, pdf pp. 192-195"]
noncomputable def toGerm (N : ℕ) [NeZero N] : X0 N →+* HGerm := toGermAux (prop2_4' N)

theorem toGerm_injective [NeZero N] : Function.Injective (toGerm N) := (toGerm N).injective

theorem toGerm_coordToX0 [NeZero N] (G : ℚ[X][X]) :
    toGerm N (coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ G)) = germ (evalJJNRat N G) :=
  toGermAux_coordToX0 _ G

theorem toGerm_jX0 [NeZero N] : toGerm N (jX0 (prop2_4' N)) = germ jFun := by
  rw [jX0, toGerm_coordToX0]
  congr 1
  funext z
  simp [evalJJNHom]

theorem toGerm_jNX0 [NeZero N] : toGerm N (jNX0 (prop2_4' N)) = germ (jN N) := by
  rw [jNX0, toGerm_coordToX0]
  congr 1
  funext z
  simp [evalJJNHom]

/-- An element of $\mathbb Q(X_0(N))$ given as a quotient $P(j, j_N)/Q(j, j_N)$. -/
noncomputable def x0Frac (N : ℕ) [NeZero N] (P Q : ℚ[X][X]) : X0 N :=
  coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ P) / coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q)

/-- If $f\,Q(j, j_N) = P(j, j_N)$ with $Q(j, j_N) \ne 0$, then the germ of `x0Frac N P Q` is that of $f$. -/
theorem toGerm_x0Frac [NeZero N] {P Q : ℚ[X][X]} {f : ℍ → ℂ} (hQ : evalJJNRat N Q ≠ 0)
    (hf : ∀ z, f z * evalJJNRat N Q z = evalJJNRat N P z) : toGerm N (x0Frac N P Q) = germ f := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQmd : MDiff (evalJJNRat N Q) := mdifferentiable_evalJJNHom _ hN Q
  have hu := isUnit_germ hQmd hQ
  have hQ' : coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q) ≠ 0 := by
    intro h0
    have := toGerm_coordToX0 (N := N) Q
    rw [h0, map_zero] at this
    exact hu.ne_zero this.symm
  have hmul : x0Frac N P Q * coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ Q) =
      coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ P) := div_mul_cancel₀ _ hQ'
  have h2 := congrArg (toGerm N) hmul
  rw [map_mul, toGerm_coordToX0, toGerm_coordToX0] at h2
  have h3 : germ (evalJJNRat N P) = germ f * germ (evalJJNRat N Q) := by
    rw [← Filter.Germ.coe_mul]
    congr 1
    funext z
    exact (hf z).symm
  rw [h3] at h2
  exact hu.mul_left_inj.1 h2

end NumberFieldKB.ModularCurves
