import NumberFieldKB.ModularCurves.Hecke
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.Germ.Basic

/-!
# The smooth affine curve $Y_0(N)$ over $\mathbb Q$: the normalization of the plane model

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 195): $X_0(N)$ over $\mathbb Q$ is the nonsingular
projective curve with function field $\mathbb Q(X_0(N)) = \mathbb Q(j, j_N)$, and $Y_0(N) = X_0(N) \smallsetminus
\{\text{cusps}\}$ is the part where $j$ is finite. Algebraically, the coordinate ring of the smooth affine curve
$Y_0(N)$ is the integral closure of $\mathbb Q[j]$ in $\mathbb Q(X_0(N))$ (`Y0Ring N`, Mathlib's
`FunctionField.ringOfIntegers`), a Dedekind domain. Its maximal ideals are the closed points of $Y_0(N)$
(`Y0Point N`). The coordinate ring $\mathbb Q[X, Y]/(F_N)$ of the plane model lies in it (`coordToY0`, injective):
`Y0Ring N` is the normalization of the plane model, which is singular in general (Milne's Remark 2.6).
-/

open Polynomial Filter
open UpperHalfPlane hiding I

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N : ℕ} [NeZero N]

instance (N : ℕ) [NeZero N] : FunctionField ℚ (X0 N) := functionField_X0

/-- **The coordinate ring of $Y_0(N)$ over $\mathbb Q$**: the integral closure of $\mathbb Q[j]$ in
$\mathbb Q(X_0(N))$. -/
@[kb "milne2006ec" "Ch. V, §2, Y_0(N) over Q, the nonsingular model of F_N = 0 (running text), pdf p. 195"]
abbrev Y0Ring (N : ℕ) [NeZero N] : Type := FunctionField.ringOfIntegers ℚ (X0 N)

example : IsDedekindDomain (Y0Ring N) := inferInstance

example : IsFractionRing (Y0Ring N) (X0 N) := inferInstance

/-- The closed points of $Y_0(N)$ over $\mathbb Q$: the maximal ideals of `Y0Ring N`. -/
abbrev Y0Point (N : ℕ) [NeZero N] : Type := IsDedekindDomain.HeightOneSpectrum (Y0Ring N)

theorem jNX0_eq_root : jNX0 (prop2_4' N) = AdjoinRoot.root _ := by
  rw [jNX0, coordToX0_mk, Polynomial.map_X]
  rfl

/-- $j_N$ is integral over $\mathbb Q[j]$ ($F_N$ is monic in $Y$). -/
theorem isIntegral_jNX0 : IsIntegral ℚ[X] (jNX0 (prop2_4' N)) := by
  refine ⟨modPoly N, modPoly_monic, ?_⟩
  rw [jNX0_eq_root, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) (X0 N), ← eval₂_map,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

theorem coordToX0_eq_aeval (G : ℚ[X][X]) :
    coordToX0 (prop2_4' N) (Ideal.Quotient.mk _ G) = aeval (jNX0 (prop2_4' N)) G := by
  rw [coordToX0_mk, ← AdjoinRoot.aeval_eq, jNX0_eq_root, aeval_map_algebraMap]

/-- The plane model's coordinate ring lies in the integral closure: $\mathbb Q[j, j_N] \subseteq \mathcal O(Y_0(N))$. -/
theorem coordToX0_mem (x : coordRingX0 N) : coordToX0 (prop2_4' N) x ∈ integralClosure ℚ[X] (X0 N) := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coordToX0_eq_aeval]
  have h := (aeval (⟨jNX0 (prop2_4' N), isIntegral_jNX0⟩ : integralClosure ℚ[X] (X0 N)) G).2
  have e := Polynomial.aeval_algHom_apply (integralClosure ℚ[X] (X0 N)).val
    (⟨jNX0 (prop2_4' N), isIntegral_jNX0⟩ : integralClosure ℚ[X] (X0 N)) G
  simp only [Subalgebra.coe_val] at e
  rw [e]
  exact h

/-- **The normalization map** $\mathbb Q[X, Y]/(F_N) \to \mathcal O(Y_0(N))$ (injective): the smooth affine curve
$Y_0(N)$ maps onto the plane model $F_N = 0$. -/
noncomputable def coordToY0 : coordRingX0 N →+* Y0Ring N :=
  (coordToX0 (prop2_4' N)).codRestrict (integralClosure ℚ[X] (X0 N)).toSubring coordToX0_mem

theorem coordToY0_injective : Function.Injective (coordToY0 (N := N)) := fun _ _ h =>
  coordToX0_injective (prop2_4' N) (congrArg Subtype.val h)

/-- $\mathcal O(Y_0(N))$ is a finitely generated $\mathbb Q[j]$-module (of rank $(\Gamma_0(1) : \Gamma_0(N))$). -/
example : Module.Finite ℚ[X] (Y0Ring N) := inferInstance

/-! ### The degeneracy maps on $Y_0$ -/

variable {M : ℕ} [NeZero M]

theorem algebraMap_polyX_X0 : algebraMap ℚ[X] (X0 M) X = jX0 (prop2_4' M) := by
  rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) (X0 M), RatFunc.algebraMap_X, algebraMap_X_X0]

theorem algebraMap_polyX0_eq : algebraMap ℚ[X] (X0 M) = (aeval (jX0 (prop2_4' M))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_rat ((algebraMap ℚ[X] (X0 M)).comp C)
      (((aeval (jX0 (prop2_4' M))).toRingHom).comp C)) a
  · rw [algebraMap_polyX_X0]
    simp

/-- $G(j, y)$ on germs, for $y$ the function $f_y$. -/
theorem toGerm_eval₂_algebraMap {y : X0 M} {fy : ℍ → ℂ} (hy : toGerm M y = germ fy) (G : ℚ[X][X]) :
    toGerm M (G.eval₂ (algebraMap ℚ[X] (X0 M)) y) = germ (fun z =>
      ((G.map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jFun z))).eval (fy z)) := by
  have hx := toGerm_jX0 (N := M)
  rw [algebraMap_polyX0_eq]
  have key : (toGerm M).comp (eval₂RingHom (aeval (jX0 (prop2_4' M))).toRingHom y) =
      (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
        (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (jFun z)).comp
          (mapRingHom (algebraMap ℚ ℂ))))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat
          ((((toGerm M).comp (eval₂RingHom (aeval (jX0 (prop2_4' M))).toRingHom y)).comp C).comp C)
          ((((Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
            (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (jFun z)).comp
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

/-- $j_d$ is integral over $\mathbb Q[j]$ in $\mathbb Q(X_0(M))$, $d \mid M$: a root of $F_d(j, Y)$. -/
theorem isIntegral_jNElt {d : ℕ} (hd : d ∣ M) : IsIntegral ℚ[X] (jNElt M d hd) := by
  have : NeZero d := ⟨by have := one_le_of_dvd hd; omega⟩
  refine ⟨modPoly d, modPoly_monic, ?_⟩
  apply toGerm_injective (N := M)
  rw [toGerm_eval₂_algebraMap (toGerm_jNElt hd), map_zero]
  have h0 : (fun z => (((modPoly d).map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jFun z))).eval
      (jN d z)) = 0 := funext fun z => evalJJN_modPolyCM (M := d) z
  rw [h0]
  rfl

theorem degeneracy_comp_algebraMap {d : ℕ} (h : d * N ∣ M) :
    (degeneracy N M d h).comp (algebraMap ℚ[X] (X0 N)) =
      (aeval (jNElt M d (dvd_trans (dvd_mul_right d N) h))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_rat (((degeneracy N M d h).comp (algebraMap ℚ[X] (X0 N))).comp C)
      (((aeval (jNElt M d (dvd_trans (dvd_mul_right d N) h))).toRingHom).comp C)) a
  · rw [RingHom.comp_apply, algebraMap_polyX_X0, degeneracy_jX0]
    simp

/-- A ring map $\iota : \mathbb Q(X_0(N)) \to \mathbb Q(X_0(M))$ sending $j$ to an element integral over
$\mathbb Q[j]$ preserves integrality over $\mathbb Q[j]$. -/
theorem isIntegral_map_of_comp (ι : X0 N →+* X0 M) {y : X0 M} (hy : IsIntegral ℚ[X] y)
    (hι : ι.comp (algebraMap ℚ[X] (X0 N)) = (aeval y).toRingHom) {x : X0 N} (hx : IsIntegral ℚ[X] x) :
    IsIntegral ℚ[X] (ι x) := by
  set S := integralClosure ℚ[X] (X0 M)
  let φ : ℚ[X] →+* S := (aeval (⟨y, hy⟩ : S)).toRingHom
  obtain ⟨p, hpm, hp⟩ := hx
  have hc : (algebraMap S (X0 M)).comp φ = ι.comp (algebraMap ℚ[X] (X0 N)) := by
    rw [hι]
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat (((algebraMap S (X0 M)).comp φ).comp C)
        (((aeval y).toRingHom).comp C)) a
    · simp [φ]
  have h1 : IsIntegral S (ι x) := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]
  exact isIntegral_trans _ h1

/-- The degeneracy maps preserve integrality over $\mathbb Q[j]$. -/
theorem isIntegral_degeneracy {d : ℕ} (h : d * N ∣ M) {x : X0 N} (hx : IsIntegral ℚ[X] x) :
    IsIntegral ℚ[X] (degeneracy N M d h x) :=
  isIntegral_map_of_comp _ (isIntegral_jNElt _) (degeneracy_comp_algebraMap h) hx

theorem frickeX0_comp_algebraMap :
    (frickeX0 (prop2_4' N)).toRingHom.comp (algebraMap ℚ[X] (X0 N)) = (aeval (jNX0 (prop2_4' N))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_rat (((frickeX0 (prop2_4' N)).toRingHom.comp
      (algebraMap ℚ[X] (X0 N))).comp C) (((aeval (jNX0 (prop2_4' N))).toRingHom).comp C)) a
  · rw [RingHom.comp_apply, algebraMap_polyX_X0]
    simp [frickeX0_jX0]

/-- **The Fricke involution is an automorphism of $Y_0(N)$ over $\mathbb Q$**: $w_N$ preserves
$\mathcal O(Y_0(N))$ ($j_N$ is integral over $\mathbb Q[j]$). -/
@[kb "milne2006ec" "Ch. V, §2, w_N is an involution of X_0(N) over Q (running text), pdf p. 194"]
noncomputable def frickeY0 (N : ℕ) [NeZero N] : Y0Ring N ≃+* Y0Ring N where
  toFun x := ⟨frickeX0 (prop2_4' N) x, isIntegral_map_of_comp (frickeX0 (prop2_4' N)).toRingHom
    isIntegral_jNX0 frickeX0_comp_algebraMap x.2⟩
  invFun x := ⟨frickeX0 (prop2_4' N) x, isIntegral_map_of_comp (frickeX0 (prop2_4' N)).toRingHom
    isIntegral_jNX0 frickeX0_comp_algebraMap x.2⟩
  left_inv _ := Subtype.ext (frickeX0_frickeX0 _ _)
  right_inv _ := Subtype.ext (frickeX0_frickeX0 _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- **The degeneracy map on $Y_0$**: $\mathcal O(Y_0(N)) \to \mathcal O(Y_0(M))$ for $dN \mid M$, i.e. the morphism
$Y_0(M) \to Y_0(N)$, $z \mapsto dz$, of smooth affine curves over $\mathbb Q$. -/
noncomputable def degeneracyY0 (N M d : ℕ) [NeZero N] [NeZero M] (h : d * N ∣ M) : Y0Ring N →+* Y0Ring M :=
  ((degeneracy N M d h).comp (integralClosure ℚ[X] (X0 N)).val.toRingHom).codRestrict
    (integralClosure ℚ[X] (X0 M)).toSubring fun x => isIntegral_degeneracy h x.2

theorem degeneracyY0_coe {d : ℕ} (h : d * N ∣ M) (x : Y0Ring N) :
    (degeneracyY0 N M d h x : X0 M) = degeneracy N M d h x := rfl

theorem degeneracyY0_injective {d : ℕ} (h : d * N ∣ M) : Function.Injective (degeneracyY0 N M d h) :=
  fun _ _ hab => Subtype.ext ((degeneracy N M d h).injective (congrArg Subtype.val hab))

/-! ### The maps on points -/

/-- $F_d(j_d, j) = 0$ on $\mathbb H$ (substitute $z \mapsto w_d z = -1/(dz)$ in $F_d(j, j_d) = 0$). -/
theorem modPoly_eval_jN_jFun {d : ℕ} [NeZero d] (z : ℍ) :
    (((modPoly d).map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jN d z))).eval (jFun z) = 0 := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h := evalJJN_modPolyCM (M := d) (fricke d z)
  unfold evalJJN at h
  rwa [jFun_fricke hd, jN_fricke hd] at h

/-- $G(x, y)$ on germs, for $x$, $y$ the functions $f_x$, $f_y$. -/
theorem toGerm_eval₂_aeval {x y : X0 M} {fx fy : ℍ → ℂ} (hx : toGerm M x = germ fx)
    (hy : toGerm M y = germ fy) (G : ℚ[X][X]) :
    toGerm M (G.eval₂ (aeval x).toRingHom y) = germ (fun z =>
      ((G.map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (fx z))).eval (fy z)) := by
  have key : (toGerm M).comp (eval₂RingHom (aeval x).toRingHom y) =
      (Filter.Germ.coeRingHom (codiscrete ℍ)).comp (RingHom.pi fun z =>
        (evalRingHom (fy z)).comp (mapRingHom ((evalRingHom (fx z)).comp
          (mapRingHom (algebraMap ℚ ℂ))))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat
          ((((toGerm M).comp (eval₂RingHom (aeval x).toRingHom y)).comp C).comp C)
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

/-- $j$ as an element of $\mathcal O(Y_0(M))$. -/
noncomputable def jY0 (M : ℕ) [NeZero M] : Y0Ring M :=
  ⟨jX0 (prop2_4' M), by rw [← algebraMap_polyX_X0]; exact isIntegral_algebraMap⟩

/-- $j$ is integral over the image of $\mathcal O(Y_0(N))$ under $z \mapsto dz$: a root of $F_d(j_d, Y)$. -/
theorem isIntegralElem_jY0 {d : ℕ} (h : d * N ∣ M) : (degeneracyY0 N M d h).IsIntegralElem (jY0 M) := by
  set hd := dvd_trans (dvd_mul_right d N) h
  have : NeZero d := ⟨by have := one_le_of_dvd hd; omega⟩
  refine ⟨(modPoly d).map (algebraMap ℚ[X] (Y0Ring N)), modPoly_monic.map _, ?_⟩
  apply Subtype.ext
  rw [eval₂_map]
  have hcoe : ((integralClosure ℚ[X] (X0 M)).val.toRingHom.comp
      ((degeneracyY0 N M d h).comp (algebraMap ℚ[X] (Y0Ring N)))) =
      (degeneracy N M d h).comp (algebraMap ℚ[X] (X0 N)) := by
    ext p
    · simp [degeneracyY0_coe]
    · simp [degeneracyY0_coe]
      rfl
  have h1 : ((Polynomial.eval₂ ((degeneracyY0 N M d h).comp (algebraMap ℚ[X] (Y0Ring N))) (jY0 M)
      (modPoly d) : Y0Ring M) : X0 M) = (modPoly d).eval₂ ((degeneracy N M d h).comp
        (algebraMap ℚ[X] (X0 N))) (jX0 (prop2_4' M)) := by
    rw [← hcoe]
    exact (Polynomial.hom_eval₂ _ _ (integralClosure ℚ[X] (X0 M)).val.toRingHom _)
  rw [h1, degeneracy_comp_algebraMap, ZeroMemClass.coe_zero]
  apply toGerm_injective (N := M)
  rw [toGerm_eval₂_aeval (toGerm_jNElt hd) toGerm_jX0, map_zero]
  have h0 : (fun z => (((modPoly d).map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom (jN d z))).eval
      (jFun z)) = 0 := funext fun z => modPoly_eval_jN_jFun z
  rw [h0]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- **$z \mapsto dz$ is a finite morphism $Y_0(M) \to Y_0(N)$**: $\mathcal O(Y_0(M))$ is integral over the image of
$\mathcal O(Y_0(N))$. -/
theorem degeneracyY0_isIntegral {d : ℕ} (h : d * N ∣ M) : (degeneracyY0 N M d h).IsIntegral := by
  letI : Algebra (Y0Ring N) (Y0Ring M) := (degeneracyY0 N M d h).toAlgebra
  intro y
  set S := Algebra.adjoin (Y0Ring N) ({jY0 M} : Set (Y0Ring M)) with hS
  have hjint : IsIntegral (Y0Ring N) (jY0 M) := isIntegralElem_jY0 h
  haveI : Algebra.IsIntegral (Y0Ring N) S :=
    Algebra.IsIntegral.adjoin fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hjint
  have hy : IsIntegral ℚ[X] y := Algebra.IsIntegral.isIntegral y
  obtain ⟨p, hpm, hp⟩ := hy
  let ψ : ℚ[X] →+* S := eval₂RingHom ((algebraMap (Y0Ring N) S).comp ((algebraMap ℚ[X] (Y0Ring N)).comp C))
    ⟨jY0 M, Algebra.subset_adjoin rfl⟩
  have hψ : (algebraMap S (Y0Ring M)).comp ψ = algebraMap ℚ[X] (Y0Ring M) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat (((algebraMap S (Y0Ring M)).comp ψ).comp C)
        ((algebraMap ℚ[X] (Y0Ring M)).comp C)) a
    · simp only [RingHom.comp_apply, ψ, coe_eval₂RingHom, eval₂_X]
      apply Subtype.ext
      exact algebraMap_polyX_X0.symm
  have h1 : IsIntegral S y := ⟨p.map ψ, hpm.map ψ, by rw [eval₂_map, hψ]; exact hp⟩
  exact isIntegral_trans y h1

/-- **The map on points** $Y_0(M) \to Y_0(N)$ induced by $z \mapsto dz$ ($dN \mid M$): a closed point $Q$ goes to
$Q \cap \mathcal O(Y_0(N))$. -/
noncomputable def degeneracyPoint {d : ℕ} (h : d * N ∣ M) (Q : Y0Point M) : Y0Point N where
  asIdeal := Q.asIdeal.comap (degeneracyY0 N M d h)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    letI : Algebra (Y0Ring N) (Y0Ring M) := (degeneracyY0 N M d h).toAlgebra
    haveI : Algebra.IsIntegral (Y0Ring N) (Y0Ring M) := ⟨degeneracyY0_isIntegral h⟩
    intro h0
    exact Q.ne_bot (Ideal.eq_bot_of_under_eq_bot h0)

/-- **The Hecke correspondence $T(p)$ on the points of $Y_0(N)$** (Milne V §4, D138): a point $Q$ of $Y_0(pN)$ gives
the pair of points (image under $z \mapsto z$, image under $z \mapsto pz$) of $Y_0(N)$. -/
noncomputable def heckePoints (N p : ℕ) [NeZero N] [NeZero p] (Q : Y0Point (p * N)) : Y0Point N × Y0Point N :=
  (degeneracyPoint (one_mul_dvd_mul N p) Q, degeneracyPoint (d := p) dvd_rfl Q)

end NumberFieldKB.ModularCurves
