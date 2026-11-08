import NumberFieldKB.Ideles.Norm
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeNorm
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal

/-!
# The relative norm of ideles and idele classes (the input `IdelicNormInput`)

$K/k$ is a finite extension of number fields and $b$ a $k$-basis of $K$. QuadFormsKB's base change
$\Psi : \mathbb A_k^\iota\cong\mathbb A_K$ (`adeleBaseChange b`) turns multiplication by $y\in\mathbb A_K$ into a matrix
$M(y)$ over $\mathbb A_k$ (`adeleLmat b y`), and its adelic norm is $N_{K/k}(y) = \det M(y)$ (`adeleNorm b`). This file
transports it to Mathlib's ideles and idele class groups and proves its local description at a finite place.

* **`ideleRelNorm b : IdeleGroup (𝓞 K) K →ₜ* IdeleGroup (𝓞 k) k`**, a continuous homomorphism
  (`continuous_adeleNorm`: $\det M(y)$ is a polynomial in the entries of $M(y)$, which are continuous in $y$), with
  `ideleRelNorm_unitEmbedding`: it sends the principal idele of $\xi\in K^\times$ to that of $N_{K/k}(\xi)$.
* **`ideleClassRelNorm b : IdeleClassGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 k) k`**, the induced map.
* **`ideleRelNorm_ofAdicCompletion`** (the local description): for a finite place $\mathfrak P$ of $K$ over the place
  $\mathfrak p$ of $k$ (`underPlace`) and $u\in K_{\mathfrak P}^\times$, the norm of the idele $u$ (at $\mathfrak P$,
  $1$ elsewhere) is an idele $z$ at $\mathfrak p$ ($1$ elsewhere) with $v_{\mathfrak p}(z) = f\,v_{\mathfrak P}(u)$,
  $f = f(\mathfrak P\mid\mathfrak p)$ (Mathlib's `Ideal.inertiaDeg`).

*Proof of the local description, without local field theory.* **Support:** with $e_{\mathfrak p}\in\mathbb A_{k,f}$ the
idempotent at $\mathfrak p$ and $E = (1, 1-e_{\mathfrak p})\in\mathbb A_k$, the image $\iota(E)\in\mathbb A_K$ is $0$
exactly at the places over $\mathfrak p$ (QuadFormsKB's `finMap_eAdele_apply`), so $\iota(E)\,y = \iota(E)$ for
$y = u$ at $\mathfrak P$. Since $M(\iota(t)) = t\cdot 1$ (`adeleLmat_adeleMap`, the $\mathbb A_k$-linearity of
$\Psi$), $\det M(y)\cdot E^{n} = E^{n}$, and $E^n = E$: the norm is $1$ at every place other than $\mathfrak p$.
**Valuation:** QuadFormsKB's `ideleNorm_adeleNorm` ($\|N_{K/k}y\| = \|y\|$, the Haar modulus is intrinsic) gives
$\|z\|_{\mathfrak p} = \|u\|_{\mathfrak P}$, that is $N\mathfrak p^{\log v(z)} = N\mathfrak P^{\log v(u)}$, and
$N\mathfrak P = N\mathfrak p^{f}$ (`Ideal.absNorm_pow_inertiaDeg`).

Same map as Tau Ceti's `ideleNormMap`/`ideleClassNormMap` (Tau Ceti, `TauCeti/NumberTheory/NumberField/Global/Ideles/
Norm/Relative.lean`, Apache-2.0; on Lean v4.36.0-rc1, cited and not imported), which also defines it as the restriction
of an adelic norm, and Neukirch, *Algebraic Number Theory*, Ch. VI, §2 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding Matrix
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped NNReal

namespace NumberFieldKB.Ideles

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K)

/-! ### Continuity of the adelic norm -/

/-- $y\mapsto\det M(y)$ on all of $\mathbb A_K$, a monoid homomorphism. -/
def adeleDet : Adeles K →* Adeles k where
  toFun y := (adeleLmat b y).det
  map_one' := by rw [adeleLmat_one, det_one]
  map_mul' y z := by rw [adeleLmat_mul, det_mul]

theorem adeleDet_apply (y : Adeles K) : adeleDet b y = (adeleLmat b y).det := rfl

omit [DecidableEq ι] in
theorem continuous_adeleLmat : Continuous (adeleLmat b) :=
  continuous_matrix fun i _ =>
    (continuous_apply i).comp ((adeleBaseChange b).symm.continuous.comp (continuous_id.mul continuous_const))

theorem continuous_adeleDet : Continuous (adeleDet b) := (continuous_adeleLmat b).matrix_det

theorem adeleNorm_eq_units_map : adeleNorm b = Units.map (adeleDet b) :=
  MonoidHom.ext fun _ => Units.ext rfl

/-- **The adelic norm is continuous** on ideles (units topology). -/
theorem continuous_adeleNorm : Continuous (adeleNorm b) := by
  rw [adeleNorm_eq_units_map]
  exact Continuous.units_map _ (continuous_adeleDet b)

/-- $M(\iota(t)) = t\cdot1$ for $t\in\mathbb A_k$ ($\mathbb A_k$-linearity of $\Psi$). -/
theorem adeleLmat_adeleMap (t : Adeles k) : adeleLmat b (adeleMap k K t) = Matrix.scalar ι t :=
  adeleLmat_ext b fun a => by
    rw [adeleBaseChange_mulVec_adeleLmat, ← adeleBaseChange_smul]
    congr 1
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-! ### The relative norm on Mathlib's ideles and idele classes -/

/-- **The relative norm of ideles** $N_{K/k} : \mathbb I_K\to\mathbb I_k$ on Mathlib's idele groups: QuadFormsKB's
`adeleNorm b` ($y\mapsto\det M(y)$) through `ideleGroupEquiv`. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on I_L) [unverified locator]"]
def ideleRelNorm : IdeleGroup (𝓞 K) K →ₜ* IdeleGroup (𝓞 k) k where
  toMonoidHom := ((ideleGroupEquiv k).symm : (Adeles k)ˣ →* IdeleGroup (𝓞 k) k).comp
    ((adeleNorm b).comp (ideleGroupEquiv K : IdeleGroup (𝓞 K) K →* (Adeles K)ˣ))
  continuous_toFun :=
    (ideleGroupEquiv k).symm.continuous.comp ((continuous_adeleNorm b).comp (ideleGroupEquiv K).continuous)

theorem ideleGroupEquiv_ideleRelNorm (x : IdeleGroup (𝓞 K) K) :
    ideleGroupEquiv k (ideleRelNorm b x) = adeleNorm b (ideleGroupEquiv K x) :=
  (ideleGroupEquiv k).apply_symm_apply _

/-- The relative norm of a principal idele is the principal idele of the field norm. -/
theorem ideleRelNorm_unitEmbedding (ξ : Kˣ) :
    ideleRelNorm b (IdeleGroup.unitEmbedding (𝓞 K) K ξ) =
      IdeleGroup.unitEmbedding (𝓞 k) k (Units.map (Algebra.norm k : K →* k) ξ) := by
  apply (ideleGroupEquiv k).injective
  rw [ideleGroupEquiv_ideleRelNorm, ideleGroupEquiv_unitEmbedding, adeleNorm_diagUnits,
    ideleGroupEquiv_unitEmbedding]

theorem principalSubgroup_le_comap_ideleRelNorm :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤
      (IdeleGroup.principalSubgroup (𝓞 k) k).comap (ideleRelNorm b).toMonoidHom := by
  rintro _ ⟨ξ, rfl⟩
  exact ⟨_, (ideleRelNorm_unitEmbedding b ξ).symm⟩

/-- **The relative norm of idele classes** $N_{K/k} : C_K\to C_k$, induced by `ideleRelNorm b`. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on C_L) [unverified locator]"]
def ideleClassRelNorm : IdeleClassGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 k) k where
  toMonoidHom := QuotientGroup.map _ _ (ideleRelNorm b).toMonoidHom (principalSubgroup_le_comap_ideleRelNorm b)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (ideleRelNorm b).continuous)

theorem ideleClassRelNorm_mk (x : IdeleGroup (𝓞 K) K) :
    ideleClassRelNorm b (x : IdeleClassGroup (𝓞 K) K) = ((ideleRelNorm b x : IdeleGroup (𝓞 k) k) : _) := rfl

/-! ### The local description at a finite place -/

theorem finiteOfAdicCompletion_self {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : FiniteAdeleRing.ofAdicCompletion F v x v = x := by
  classical
  exact Pi.mulSingle_eq_same v x

theorem finiteOfAdicCompletion_of_ne {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)}
    (h : w ≠ v) (x : v.adicCompletion F) : FiniteAdeleRing.ofAdicCompletion F v x w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h x

/-- The norm of an idele concentrated at one finite place is the norm of its coordinate there. -/
theorem norm_ofAdicCompletion {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    ‖((IdeleGroup.ofAdicCompletion (𝓞 F) F v u : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)‖ =
      ‖(u : v.adicCompletion F)‖ := by
  rw [AdeleRing.norm_apply_of_isUnit (Units.isUnit _)]
  have h1 : ∀ w : InfinitePlace F,
      ‖((IdeleGroup.ofAdicCompletion (𝓞 F) F v u : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult = 1 := by
    intro w
    show ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1
    rw [Pi.one_apply, norm_one, one_pow]
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul, finprod_eq_single _ v]
  · exact congrArg norm (finiteOfAdicCompletion_self v (u : v.adicCompletion F))
  · intro w hw
    show ‖FiniteAdeleRing.ofAdicCompletion F v (u : v.adicCompletion F) w‖ = 1
    rw [finiteOfAdicCompletion_of_ne hw, norm_one]

variable (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)

/-- The idempotent $E = (1, 1-e_{\mathfrak p})\in\mathbb A_k$: $1$ at every place except $\mathfrak p$. -/
def offPlace (p : HeightOneSpectrum (𝓞 k)) : Adeles k := (1, 1 - eAdele p)

theorem offPlace_mul_self (p : HeightOneSpectrum (𝓞 k)) : offPlace p * offPlace p = offPlace p := by
  refine Prod.ext (mul_one _) ?_
  show (1 - eAdele p) * (1 - eAdele p) = 1 - eAdele p
  rw [sub_mul, one_mul, mul_sub, mul_one, eAdele_mul_self, sub_self, sub_zero]

/-- **Support**: $\iota(E)\,y = \iota(E)$ for the idele $y$ that is $u$ at $\mathfrak P$ and $1$ elsewhere,
$E$ = `offPlace` of the place below $\mathfrak P$. -/
theorem adeleMap_offPlace_mul :
    adeleMap k K (offPlace (underPlace (k := k) v)) *
        ((ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : (Adeles K)ˣ) : Adeles K) =
      adeleMap k K (offPlace (underPlace (k := k) v)) := by
  classical
  refine Prod.ext ?_ ?_
  · show infRingHom k K 1 * InfiniteAdeleRing.ringEquiv_mixedSpace K 1 = infRingHom k K 1
    rw [map_one, map_one, mul_one]
  · refine FiniteAdeleRing.ext K fun w => ?_
    show (finMap k K (1 - eAdele (underPlace (k := k) v))) w *
        (FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K)) w =
      (finMap k K (1 - eAdele (underPlace (k := k) v))) w
    rw [map_sub, map_one]
    show ((1 : FiniteAdeleRing (𝓞 K) K) w - (finMap k K (eAdele (underPlace (k := k) v))) w) *
        (FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K)) w =
      (1 : FiniteAdeleRing (𝓞 K) K) w - (finMap k K (eAdele (underPlace (k := k) v))) w
    rw [finMap_eAdele_apply, show (1 : FiniteAdeleRing (𝓞 K) K) w = 1 from rfl]
    by_cases hw : w = v
    · subst hw
      rw [ite_eq_left rfl, sub_self, zero_mul]
    · rw [finiteOfAdicCompletion_of_ne hw, mul_one]

/-- **The norm of a local idele is supported at the place below**: $N(y)\cdot E = E$. -/
theorem adeleNorm_mul_offPlace :
    ((adeleNorm b (ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) : (Adeles k)ˣ) : Adeles k) *
        offPlace (underPlace (k := k) v) = offPlace (underPlace (k := k) v) := by
  set y := ((ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : (Adeles K)ˣ) : Adeles K)
  set E := offPlace (k := k) (underPlace (k := k) v)
  have hM : adeleLmat b y * Matrix.scalar ι E = Matrix.scalar ι E := by
    rw [← adeleLmat_adeleMap (K := K) b E, ← adeleLmat_mul, mul_comm, adeleMap_offPlace_mul]
  have hdet := congrArg Matrix.det hM
  rw [det_mul, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  have hidem : IsIdempotentElem E := offPlace_mul_self _
  have hn : Fintype.card ι ≠ 0 := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos.ne'
  rw [hidem.pow_eq hn] at hdet
  exact hdet

/-- **The local norm** $z\in k_{\mathfrak p}^\times$: the $\mathfrak p$-coordinate of $N_{K/k}(y)$ for the idele $y$
that is $u$ at $\mathfrak P$ and $1$ elsewhere ($\mathfrak p$ = `underPlace v`). It is $N_{K_{\mathfrak P}/k_{\mathfrak p}}(u)$
[not proved here; not needed]. -/
def localNorm : ((underPlace (k := k) v).adicCompletion k)ˣ :=
  Units.map ((evAdele (underPlace (k := k) v)).toMonoidHom.comp (MonoidHom.snd _ _))
    (adeleNorm b (ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)))

/-- **The norm of a local idele is local**: $N_{K/k}(y)$ is the idele that is `localNorm b v u` at $\mathfrak p$ and
$1$ elsewhere. -/
theorem adeleNorm_ofAdicCompletion :
    adeleNorm b (ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) =
      ideleGroupEquiv k (IdeleGroup.ofAdicCompletion (𝓞 k) k (underPlace (k := k) v) (localNorm b v u)) := by
  classical
  have h := adeleNorm_mul_offPlace b v u
  apply Units.ext
  refine Prod.ext ?_ ?_
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_mul, offPlace, mul_one] at h1
    rw [h1]
    show (1 : mixedSpace k) = InfiniteAdeleRing.ringEquiv_mixedSpace k 1
    rw [map_one]
  · refine FiniteAdeleRing.ext k fun l => ?_
    have h2 := congrArg (fun a : Adeles k => evAdele l a.2) h
    simp only [Prod.snd_mul, offPlace, map_mul, map_sub, map_one, evAdele_apply, eAdele_apply] at h2
    by_cases hl : l = underPlace (k := k) v
    · subst hl
      show _ = FiniteAdeleRing.ofAdicCompletion k (underPlace (k := k) v) _ (underPlace (k := k) v)
      rw [finiteOfAdicCompletion_self]
      rfl
    · rw [ite_eq_right hl, sub_zero, mul_one] at h2
      rw [h2]
      show _ = FiniteAdeleRing.ofAdicCompletion k (underPlace (k := k) v) _ l
      rw [finiteOfAdicCompletion_of_ne hl]

/-- $\|z\|_{\mathfrak p} = \|u\|_{\mathfrak P}$ for $z$ = `localNorm b v u` (QuadFormsKB's `ideleNorm_adeleNorm`). -/
theorem norm_localNorm :
    ‖((localNorm b v u : ((underPlace (k := k) v).adicCompletion k)ˣ) : (underPlace (k := k) v).adicCompletion k)‖ =
      ‖(u : v.adicCompletion K)‖ := by
  have h := ideleNorm_adeleNorm b (ideleGroupEquiv K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u))
  rw [adeleNorm_ofAdicCompletion, ← norm_eq_ideleNorm, ← norm_eq_ideleNorm, norm_ofAdicCompletion,
    norm_ofAdicCompletion] at h
  exact h

/-- The norm of a nonzero element of $F_v$: $\|x\| = N v^{\log v(x)}$. -/
theorem norm_eq_zpow_log {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)}
    {x : w.adicCompletion F} (hx : x ≠ 0) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℝ≥0) : ℝ) ^ WithZero.log (Valued.v x) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hx),
    NNReal.coe_zpow]

/-- **$N\mathfrak P = N\mathfrak p^{f}$**, $f = f(\mathfrak P\mid\mathfrak p)$ (Mathlib's `Ideal.absNorm_pow_inertiaDeg`). -/
theorem absNorm_eq_pow_inertiaDeg :
    Ideal.absNorm v.asIdeal = Ideal.absNorm (underPlace (k := k) v).asIdeal ^ v.asIdeal.inertiaDeg (𝓞 k) :=
  (Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under (𝓞 k)) v.asIdeal).symm

/-- **The valuation of the local norm**: $v_{\mathfrak p}(z) = f\,v_{\mathfrak P}(u)$, i.e.
$v(z) = v(u)^{f}$ multiplicatively, $f = f(\mathfrak P\mid\mathfrak p)$. -/
theorem valued_localNorm :
    Valued.v ((localNorm b v u : ((underPlace (k := k) v).adicCompletion k)ˣ) : (underPlace (k := k) v).adicCompletion k) =
      Valued.v (u : v.adicCompletion K) ^ v.asIdeal.inertiaDeg (𝓞 k) := by
  set z := ((localNorm b v u : ((underPlace (k := k) v).adicCompletion k)ˣ) : (underPlace (k := k) v).adicCompletion k)
  set f := v.asIdeal.inertiaDeg (𝓞 k)
  have hz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have hu : Valued.v (u : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have h := norm_localNorm b v u
  rw [norm_eq_zpow_log (Units.ne_zero _), norm_eq_zpow_log (Units.ne_zero _), absNorm_eq_pow_inertiaDeg (k := k) v,
    Nat.cast_pow, NNReal.coe_pow, ← zpow_natCast, ← _root_.zpow_mul] at h
  have hp : (1 : ℝ) < ((Ideal.absNorm (underPlace (k := k) v).asIdeal : ℝ≥0) : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm_nnreal (underPlace (k := k) v)
  have hlog : WithZero.log (Valued.v z) = f * WithZero.log (Valued.v (u : v.adicCompletion K)) :=
    zpow_right_injective₀ (by positivity) hp.ne' h
  rw [← WithZero.exp_log hz, hlog, ← WithZero.exp_log hu, WithZero.log_exp, ← WithZero.exp_nsmul, nsmul_eq_mul]

/-- **Local description on Mathlib's ideles**: the norm of the idele $u$ at $\mathfrak P$ is the idele
$z$ = `localNorm b v u` at the place $\mathfrak p$ below. -/
theorem ideleRelNorm_ofAdicCompletion :
    ideleRelNorm b (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) =
      IdeleGroup.ofAdicCompletion (𝓞 k) k (underPlace (k := k) v) (localNorm b v u) := by
  apply (ideleGroupEquiv k).injective
  rw [ideleGroupEquiv_ideleRelNorm, adeleNorm_ofAdicCompletion]

/-- **Local description on idele classes**: $N_{K/k}$ of the class of $u\in K_{\mathfrak P}^\times$ is the class of
$z$ = `localNorm b v u` $\in k_{\mathfrak p}^\times$, and $v(z) = v(u)^{f(\mathfrak P\mid\mathfrak p)}$
(`valued_localNorm`). -/
@[kb "neukirch1999" "Ch. VI, §2 (N_{L|K} on I_L is the product of the local norms) [unverified locator]"]
theorem ideleClassRelNorm_ofAdicCompletion :
    ideleClassRelNorm b (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      IdeleClassGroup.ofAdicCompletion (𝓞 k) k (underPlace (k := k) v) (localNorm b v u) := by
  show ideleClassRelNorm b ((IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleGroup (𝓞 K) K) : _) = _
  rw [ideleClassRelNorm_mk, ideleRelNorm_ofAdicCompletion]
  rfl

end

end NumberFieldKB.Ideles
