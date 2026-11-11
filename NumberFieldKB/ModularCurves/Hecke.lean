import NumberFieldKB.ModularCurves.Germs
import NumberFieldKB.MilneEC.Ch5bCorrespondences
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Degeneracy maps and the Hecke correspondences on $\mathbb Q(X_0(N))$ (algebraic half)

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §4 and §6 (pdf pp. 205–223). For $dN \mid M$ the map
$z \mapsto dz$ induces a morphism $X_0(M) \to X_0(N)$ over $\mathbb Q$; on function fields it is the embedding
$$\mathbb Q(X_0(N)) \to \mathbb Q(X_0(M)), \qquad j \mapsto j_d, \quad j_N \mapsto j_{dN}$$
(`degeneracy`), which exists because $j_d, j_{dN} \in \mathbb Q(j, j_M)$ (`exists_rat_jN_of_dvd`) and
$F_N(j_d, j_{dN}) = 0$. The Hecke correspondence $T(p)$ on $X_0(N)$ is the pair of degeneracy maps $d = 1$ and $d = p$
from $X_0(pN)$ (`heckePair`), and its action on functions is $f \mapsto \operatorname{Tr}_{\iota_1}(\iota_p(f))$
(`heckeOnFunctions`): pull back by $z \mapsto pz$, push forward along $z \mapsto z$.

Every identity is checked on germs of functions on $\mathbb H$ (`toGerm`, injective).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex Topology
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- `toGerm` composed with `aeval x` is evaluation at the function of `x`. -/
theorem toGerm_aeval {x : X0 M} {fx : ℍ → ℂ} (hx : toGerm M x = germ fx) (p : ℚ[X]) :
    toGerm M (aeval x p) = germ (fun z => (p.map (algebraMap ℚ ℂ)).eval (fx z)) := by
  have key : (toGerm M).comp (aeval x).toRingHom = (Filter.Germ.coeRingHom (codiscrete ℍ)).comp
      (RingHom.pi fun z => (evalRingHom (fx z)).comp (mapRingHom (algebraMap ℚ ℂ))) := by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : ((toGerm M).comp (aeval x).toRingHom).comp C =
          ((Filter.Germ.coeRingHom (codiscrete ℍ)).comp
            (RingHom.pi fun z => (evalRingHom (fx z)).comp (mapRingHom (algebraMap ℚ ℂ)))).comp C :=
        RingHom.ext_rat _ _
      exact RingHom.congr_fun h1 a
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hx,
        Filter.Germ.coe_coeRingHom]
      congr 1
      funext z
      simp [RingHom.pi_apply]
  exact RingHom.congr_fun key p

/-- **Embeddings of function fields checked on functions.** If $x, y \in \mathbb Q(X_0(M))$ are the functions
$f_x, f_y$, with $f_x$ holomorphic and onto $\mathbb C$ (so $x$ is transcendental over $\mathbb Q$) and
$F_N(f_x, f_y) = 0$, there is a field embedding $\mathbb Q(X_0(N)) \to \mathbb Q(X_0(M))$ with $j \mapsto x$,
$j_N \mapsto y$. -/
theorem exists_embedding {x y : X0 M} {fx fy : ℍ → ℂ} (hx : toGerm M x = germ fx)
    (hy : toGerm M y = germ fy) (hfx : MDiff fx) (hsurj : Function.Surjective fx)
    (hrel : ∀ z, (((modPoly N).map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (fx z))).eval (fy z) = 0) :
    ∃ ι : X0 N →+* X0 M, ι (jX0 (prop2_4' N)) = x ∧ ι (jNX0 (prop2_4' N)) = y := by
  -- the map on `ℚ(X)`, `X ↦ x`
  have hunit : ∀ p : nonZeroDivisors ℚ[X], IsUnit ((aeval x).toRingHom (p : ℚ[X])) := by
    intro p
    rw [isUnit_iff_ne_zero]
    intro h0
    have hp0 := nonZeroDivisors.ne_zero p.2
    have h1 := toGerm_aeval hx (p : ℚ[X])
    have hmd : MDiff (fun z => ((p : ℚ[X]).map (algebraMap ℚ ℂ)).eval (fx z)) := fun z =>
      (((p : ℚ[X]).map (algebraMap ℚ ℂ)).differentiable (fx z)).comp_mdifferentiableAt (hfx z)
    rw [show aeval x (p : ℚ[X]) = 0 from h0, map_zero, eq_comm, germ_eq_zero_iff hmd] at h1
    apply hp0
    refine (Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).1 (Polynomial.funext fun t => ?_)
    obtain ⟨z, rfl⟩ := hsurj t
    simpa using congrFun h1 z
  obtain ⟨i, hcomp⟩ : ∃ i : RatFunc ℚ →+* X0 M, i.comp (algebraMap ℚ[X] (RatFunc ℚ)) = (aeval x).toRingHom :=
    ⟨IsLocalization.lift (M := nonZeroDivisors ℚ[X]) (S := RatFunc ℚ) (g := (aeval x).toRingHom) hunit,
      RingHom.ext fun p => IsLocalization.lift_eq (M := nonZeroDivisors ℚ[X]) (S := RatFunc ℚ)
        (g := (aeval x).toRingHom) hunit p⟩
  -- `F_N(x, y) = 0`
  have h0 : ((modPoly N).map (algebraMap ℚ[X] (RatFunc ℚ))).eval₂ i y = 0 := by
    rw [eval₂_map, hcomp]
    apply toGerm_injective (N := M)
    rw [map_zero]
    have key : (toGerm M).comp (eval₂RingHom (aeval x).toRingHom y) =
        (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
          (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (fx z)).comp
            (mapRingHom (algebraMap ℚ ℂ))))) := by
      apply Polynomial.ringHom_ext'
      · apply Polynomial.ringHom_ext
        · intro a
          have := RingHom.ext_rat ((((toGerm M).comp (eval₂RingHom (aeval x).toRingHom y)).comp C).comp C)
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
    have := RingHom.congr_fun key (modPoly N)
    rw [RingHom.comp_apply, coe_eval₂RingHom] at this
    rw [this, RingHom.comp_apply, Filter.Germ.coe_coeRingHom]
    have hz : (RingHom.pi fun z => (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (fx z)).comp
        (mapRingHom (algebraMap ℚ ℂ))))) (modPoly N) = 0 := by
      funext z
      rw [RingHom.pi_apply, Pi.zero_apply, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom,
        ← Polynomial.map_map]
      exact hrel z
    rw [hz]
    rfl
  refine ⟨AdjoinRoot.lift i y h0, ?_, ?_⟩
  · rw [jX0, coordToX0_mk, AdjoinRoot.lift_mk, Polynomial.map_C, eval₂_C]
    rw [← RingHom.comp_apply, hcomp]
    simp
  · rw [jNX0, coordToX0_mk, AdjoinRoot.lift_mk, Polynomial.map_X, eval₂_X]

/-- $j_d$ is onto $\mathbb C$. -/
theorem jN_surjective {d : ℕ} (hd : 1 ≤ d) : Function.Surjective (jN d) := by
  intro t
  obtain ⟨w, rfl⟩ := jFun_surjective t
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hw : 0 < ((w : ℂ) / d).im := by
    have e : (w : ℂ) / d = (((d : ℝ)⁻¹ : ℝ) : ℂ) * w := by push_cast; field_simp
    rw [e, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.2 hdpos) w.im_pos
  refine ⟨ofComplex ((w : ℂ) / d), ?_⟩
  unfold jN
  congr 1
  ext
  rw [ofComplex_apply_of_im_pos hw]
  have h1 : 0 < ((d : ℂ) * ((w : ℂ) / d)).im := by
    have : (d : ℂ) * ((w : ℂ) / d) = w := by field_simp
    rw [this]; exact w.im_pos
  rw [ofComplex_apply_of_im_pos h1]
  field_simp

/-- $F_N(j_d, j_{dN}) = 0$ on $\mathbb H$. -/
theorem modPoly_jN_jN {d : ℕ} (hd : 1 ≤ d) (z : ℍ) :
    (((modPoly N).map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jN d z))).eval (jN (d * N) z) = 0 := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h := (prop2_4' N).exists_poly.choose_spec.2.2.1 (ofComplex ((d : ℂ) * z))
  have e1 : jFun (ofComplex ((d : ℂ) * z)) = jN d z := rfl
  have e2 : jN N (ofComplex ((d : ℂ) * z)) = jN (d * N) z := by
    unfold jN
    congr 2
    rw [coe_ofComplex_mul hd]
    push_cast
    ring
  unfold evalJJN at h
  rw [e1, e2] at h
  exact h

/-- The element $j_d$ of $\mathbb Q(X_0(M))$ for $d \mid M$ (`exists_rat_jN_of_dvd`). -/
noncomputable def jNElt (M d : ℕ) [NeZero M] (hd : d ∣ M) : X0 M :=
  x0Frac M (exists_rat_jN_of_dvd hd).choose (exists_rat_jN_of_dvd hd).choose_spec.choose

theorem toGerm_jNElt {d : ℕ} (hd : d ∣ M) : toGerm M (jNElt M d hd) = germ (jN d) :=
  toGerm_x0Frac (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.1
    (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.2

theorem one_le_of_dvd {d : ℕ} (hd : d ∣ M) : 1 ≤ d :=
  Nat.one_le_iff_ne_zero.mpr fun h0 => by
    subst h0; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd hd)

theorem exists_degeneracy (N M d : ℕ) [NeZero N] [NeZero M] (h : d * N ∣ M) :
    ∃ ι : X0 N →+* X0 M, ι (jX0 (prop2_4' N)) = jNElt M d (dvd_trans (dvd_mul_right d N) h) ∧
      ι (jNX0 (prop2_4' N)) = jNElt M (d * N) h :=
  exists_embedding (N := N) (M := M) (toGerm_jNElt (dvd_trans (dvd_mul_right d N) h))
    (toGerm_jNElt h) (jN_mdifferentiable (one_le_of_dvd (dvd_trans (dvd_mul_right d N) h)))
    (jN_surjective (one_le_of_dvd (dvd_trans (dvd_mul_right d N) h)))
    (modPoly_jN_jN (one_le_of_dvd (dvd_trans (dvd_mul_right d N) h)))

/-- **The degeneracy map** $\mathbb Q(X_0(N)) \to \mathbb Q(X_0(M))$ for $dN \mid M$, induced by
$X_0(M) \to X_0(N)$, $z \mapsto dz$: $j \mapsto j_d$, $j_N \mapsto j_{dN}$. -/
@[kb "milne2006ec" "Ch. V, §4, the maps X_0(M) → X_0(N), z ↦ dz, for dN | M (running text), pdf p. 205"]
noncomputable def degeneracy (N M d : ℕ) [NeZero N] [NeZero M] (h : d * N ∣ M) : X0 N →+* X0 M :=
  (exists_degeneracy N M d h).choose

theorem degeneracy_jX0 {d : ℕ} (h : d * N ∣ M) :
    degeneracy N M d h (jX0 (prop2_4' N)) = jNElt M d (dvd_trans (dvd_mul_right d N) h) :=
  (exists_degeneracy N M d h).choose_spec.1

theorem degeneracy_jNX0 {d : ℕ} (h : d * N ∣ M) :
    degeneracy N M d h (jNX0 (prop2_4' N)) = jNElt M (d * N) h :=
  (exists_degeneracy N M d h).choose_spec.2

theorem toGerm_degeneracy_jX0 {d : ℕ} (h : d * N ∣ M) :
    toGerm M (degeneracy N M d h (jX0 (prop2_4' N))) = germ (jN d) := by
  rw [degeneracy_jX0, toGerm_jNElt]

theorem toGerm_degeneracy_jNX0 {d : ℕ} (h : d * N ∣ M) :
    toGerm M (degeneracy N M d h (jNX0 (prop2_4' N))) = germ (jN (d * N)) := by
  rw [degeneracy_jNX0, toGerm_jNElt]

/-! ### The forgetful map $X_0(M) \to X_0(N)$ and its degree -/

theorem jNElt_one (h : 1 ∣ M) : jNElt M 1 h = jX0 (prop2_4' M) := by
  apply toGerm_injective (N := M)
  rw [toGerm_jNElt, toGerm_jX0]
  congr 1
  funext z
  unfold jN
  congr 1
  ext
  rw [coe_ofComplex_mul le_rfl]
  simp

theorem algebraMap_X_X0 : algebraMap (RatFunc ℚ) (X0 N) RatFunc.X = jX0 (prop2_4' N) := by
  rw [jX0, coordToX0_C, AdjoinRoot.algebraMap_eq, RatFunc.algebraMap_X]

/-- For $N \mid M$, the map $z \mapsto z$ is compatible with $j$: the embedding is a $\mathbb Q(j)$-algebra map. -/
theorem degeneracy_one_comp_algebraMap (h : 1 * N ∣ M) :
    (degeneracy N M 1 h).comp (algebraMap (RatFunc ℚ) (X0 N)) = algebraMap (RatFunc ℚ) (X0 M) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
  apply Polynomial.ringHom_ext
  · intro a
    have := RingHom.ext_rat
      ((((degeneracy N M 1 h).comp (algebraMap (RatFunc ℚ) (X0 N))).comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)
      (((algebraMap (RatFunc ℚ) (X0 M)).comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)
    exact RingHom.congr_fun this a
  · simp only [RingHom.comp_apply]
    rw [show algebraMap ℚ[X] (RatFunc ℚ) X = RatFunc.X from RatFunc.algebraMap_X, algebraMap_X_X0,
      algebraMap_X_X0, degeneracy_jX0, jNElt_one]

/-- $\mathbb Q(X_0(M))$ as an algebra over $\mathbb Q(X_0(N))$ via $z \mapsto z$, for $N \mid M$. -/
noncomputable abbrev forgetAlgebra (N M : ℕ) [NeZero N] [NeZero M] (h : 1 * N ∣ M) : Algebra (X0 N) (X0 M) :=
  (degeneracy N M 1 h).toAlgebra

theorem isScalarTower_forget (h : 1 * N ∣ M) :
    letI := forgetAlgebra N M h
    IsScalarTower (RatFunc ℚ) (X0 N) (X0 M) := by
  letI := forgetAlgebra N M h
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  exact (RingHom.congr_fun (degeneracy_one_comp_algebraMap h) r).symm

theorem finite_forget (h : 1 * N ∣ M) :
    letI := forgetAlgebra N M h
    Module.Finite (X0 N) (X0 M) := by
  letI := forgetAlgebra N M h
  haveI := isScalarTower_forget h
  haveI : Module.Finite (RatFunc ℚ) (X0 M) := functionField_X0
  exact Module.Finite.of_restrictScalars_finite (RatFunc ℚ) (X0 N) (X0 M)

/-- **The degree of $X_0(M) \to X_0(N)$** is $(\Gamma_0(N) : \Gamma_0(M))$, for $N \mid M$. -/
@[kb "milne2006ec" "Ch. V, §4, degree of X_0(M) → X_0(N) (running text), pdf p. 205"]
theorem finrank_forget (h : 1 * N ∣ M) :
    letI := forgetAlgebra N M h
    Module.finrank (X0 N) (X0 M) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) := by
  letI := forgetAlgebra N M h
  haveI := isScalarTower_forget h
  have hNM : N ∣ M := by simpa using h
  have hle := gamma0_le_of_dvd hNM
  have h1 := Module.finrank_mul_finrank (RatFunc ℚ) (X0 N) (X0 M)
  rw [finrank_X0, finrank_X0, ← Subgroup.relIndex_mul_index hle] at h1
  have hpos : (CongruenceSubgroup.Gamma0 N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h1

/-- **The Hecke correspondence $T(p)$ on $X_0(N)$** (Milne V §4, §6), on function fields: the two maps
$X_0(pN) \to X_0(N)$, $z \mapsto z$ and $z \mapsto pz$, as embeddings $\mathbb Q(X_0(N)) \to \mathbb Q(X_0(pN))$. -/
@[kb "milne2006ec" "Ch. V, §4, the Hecke correspondence T(p) via X_0(N) ← X_0(pN) → X_0(N), pdf p. 205"]
noncomputable def heckePair (N p : ℕ) [NeZero N] [NeZero p] :
    (X0 N →+* X0 (p * N)) × (X0 N →+* X0 (p * N)) :=
  (degeneracy N (p * N) 1 (by rw [one_mul]; exact dvd_mul_left N p),
    degeneracy N (p * N) p dvd_rfl)

theorem one_mul_dvd_mul (N p : ℕ) : 1 * N ∣ p * N := by
  rw [one_mul]
  exact dvd_mul_left N p

theorem isScalarTower_rat_forget (h : 1 * N ∣ M) :
    letI := forgetAlgebra N M h
    IsScalarTower ℚ (X0 N) (X0 M) := by
  letI := forgetAlgebra N M h
  exact IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (X0 M)) ((algebraMap (X0 N) (X0 M)).comp
      (algebraMap ℚ (X0 N)))) r

/-- **$T(p)$ acting on the function field $\mathbb Q(X_0(N))$** (Milne V §4 and Remark 7.2): the pullback of
functions by the correspondence $X_0(N) \leftarrow X_0(pN) \to X_0(N)$ (`MilneEC.pullbackFun`), i.e.
$f \mapsto \operatorname{Tr}(\iota_p(f))$: pull back along $z \mapsto pz$, push forward along $z \mapsto z$. -/
@[kb "milne2006ec" "Ch. V, §4, T(p) acting on functions on X_0(N) (running text), pdf p. 205"]
noncomputable def heckeOnFunctions (N p : ℕ) [NeZero N] [NeZero p] : X0 N →ₗ[ℚ] X0 N :=
  letI := forgetAlgebra N (p * N) (one_mul_dvd_mul N p)
  haveI := isScalarTower_rat_forget (N := N) (M := p * N) (one_mul_dvd_mul N p)
  haveI := finite_forget (N := N) (M := p * N) (one_mul_dvd_mul N p)
  NumberFieldKB.MilneEC.pullbackFun ℚ (X0 N) (X0 N) (X0 (p * N))
    (degeneracy N (p * N) p dvd_rfl).toRatAlgHom

/-- $T(p)(1) = \deg(X_0(pN) \to X_0(N)) = (\Gamma_0(N) : \Gamma_0(pN))$ ($= p + 1$ for $p \nmid N$). -/
theorem heckeOnFunctions_one (N p : ℕ) [NeZero N] [NeZero p] :
    heckeOnFunctions N p 1 =
      ((CongruenceSubgroup.Gamma0 (p * N)).relIndex (CongruenceSubgroup.Gamma0 N) : X0 N) := by
  letI := forgetAlgebra N (p * N) (one_mul_dvd_mul N p)
  haveI := isScalarTower_rat_forget (N := N) (M := p * N) (one_mul_dvd_mul N p)
  haveI := finite_forget (N := N) (M := p * N) (one_mul_dvd_mul N p)
  have h := NumberFieldKB.MilneEC.pullbackFun_algebraMap (k := ℚ) (K := X0 N) (K' := X0 N)
    (L := X0 (p * N)) (degeneracy N (p * N) p dvd_rfl).toRatAlgHom 1
  have e1 : algebraMap ℚ (X0 N) 1 = 1 := map_one _
  rw [e1, mul_one, finrank_forget] at h
  unfold heckeOnFunctions
  exact h

end NumberFieldKB.ModularCurves
