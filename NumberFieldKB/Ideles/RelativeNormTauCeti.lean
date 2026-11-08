import NumberFieldKB.Ideles.RelativeNorm
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Places.Semilocal
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
import NumberFieldKB.TauCetiPort.RingTheory.NormTrace.Pi

/-!
# Our relative idele norm is Tau Ceti's

$L/K$ is a finite extension of number fields and $b$ a $K$-basis of $L$. This library's relative norm
`ideleRelNorm b` (QuadFormsKB's $y\mapsto\det M(y)$, the determinant of multiplication on
$L\otimes_K\mathbb A_K\cong\mathbb A_L$, through `ideleGroupEquiv`) equals Tau Ceti's
`TauCeti.GlobalNumberFields.ideleNormMap K L` (the product $\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}$ of the local norms
at every place $v$; ported under `NumberFieldKB/TauCetiPort/`, Tau Ceti main `67aa1716`, Apache 2.0).

* **`adeleRingEquiv_adeleExtension`**: QuadFormsKB's natural map $\iota = $ `adeleMap K L` $:\mathbb A_K\to\mathbb A_L$
  is Tau Ceti's `adeleExtension` (componentwise the completion maps $K_v\to L_w$). Both are continuous ring
  homomorphisms extending $K\to L$ and fixing the idempotent $(1,0)$, so Tau Ceti's `AdeleRing.ringHom_ext` applies.
* **`norm_sum_tmul`**: for a commutative $K$-algebra $R$ and $c\in R^\iota$,
  $\mathrm{Nm}_{R\otimes_KL/R}(\sum_ic_i\otimes b_i) = \det\big(\sum_i c_i\,M_b(b_i)\big)$, $M_b$ = `Algebra.leftMulMatrix b`.
* **`ideleRelNorm_eq_ideleNormMap`** (the comparison): with $y = \sum_ib_i\,\iota(a_i)$
  (`adeleBaseChange_apply`), $\det M(y) = \det(\sum_ia_iM_b(b_i))$; at a place $v$ this is the norm of
  $\sum_ia_{i,v}\otimes b_i\in K_v\otimes_KL$, which Tau Ceti's semilocal decomposition
  $K_v\otimes_KL\cong\prod_{w\mid v}L_w$ (`semilocalEquiv`, `infiniteSemilocalEquiv`) turns into
  $\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}(y_w)$.

Milne, *Class Field Theory*, Chapter V, §4, p. 177, defines $\mathrm{Nm}_{L/K}$ on ideles placewise; this file shows the
two constructions agree.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding Matrix
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

namespace NumberFieldKB.Ideles

noncomputable section

/-! ### The norm on $R\otimes_K L$ in the coordinates of a basis -/

section NormForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K L)

/-- $\det\big(\sum_ic_i\,M_b(b_i)^{\varphi}\big)$ for a ring homomorphism $\varphi : K\to R$ and $c\in R^\iota$. -/
def normForm {R : Type*} [CommRing R] (φ : K →+* R) (c : ι → R) : R :=
  (∑ i, Matrix.scalar ι (c i) * (Algebra.leftMulMatrix b (b i)).map φ).det

theorem map_normForm {R S : Type*} [CommRing R] [CommRing S] (φ : K →+* R) (ψ : R →+* S) (c : ι → R) :
    ψ (normForm b φ c) = normForm b (ψ.comp φ) (fun i => ψ (c i)) := by
  rw [normForm, normForm, RingHom.map_det, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  ext j k
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite ψ]

/-- $M_{1\otimes b}(1\otimes x) = M_b(x)$ mapped to $R$. -/
theorem leftMulMatrix_basis_one_tmul (R : Type*) [CommRing R] [Algebra K R] (x : L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b) ((1 : R) ⊗ₜ[K] x) =
      (Algebra.leftMulMatrix b x).map (algebraMap K R) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rfl

/-- **The norm of $\sum_ic_i\otimes b_i$** in $R\otimes_KL$ over $R$ is $\det(\sum_ic_iM_b(b_i))$. -/
theorem norm_sum_tmul (R : Type*) [CommRing R] [Algebra K R] (c : ι → R) :
    Algebra.norm R (∑ i, c i ⊗ₜ[K] b i) = normForm b (algebraMap K R) c := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R b), normForm, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : c i ⊗ₜ[K] b i = c i • ((1 : R) ⊗ₜ[K] b i) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, leftMulMatrix_basis_one_tmul, Matrix.smul_eq_diagonal_mul]
  rfl

end NormForm

/-! ### QuadFormsKB's adele map is Tau Ceti's adele extension -/

section Adeles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **QuadFormsKB's natural map $\iota:\mathbb A_K\to\mathbb A_L$ is Tau Ceti's `adeleExtension`**, through
`adeleRingEquiv`: both are continuous ring homomorphisms extending $K\to L$ and fixing $(1,0)$. -/
theorem adeleRingEquiv_adeleExtension (t : AdeleRing (𝓞 K) K) :
    adeleRingEquiv L (NumberField.adeleExtension (𝓞 K) K (𝓞 L) L t) =
      adeleMap K L (adeleRingEquiv K t) := by
  let f : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
    ((adeleRingEquiv L).symm : Adeles L →+* AdeleRing (𝓞 L) L).comp
      ((adeleMap K L).comp (adeleRingEquiv K : AdeleRing (𝓞 K) K →+* Adeles K))
  have hf : Continuous f :=
    (continuous_adeleRingEquiv_symm L).comp (continuous_adeleMap.comp (continuous_adeleRingEquiv K))
  have h : f = NumberField.adeleExtension (𝓞 K) K (𝓞 L) L := by
    refine NumberField.AdeleRing.ringHom_ext (𝓞 K) K hf (NumberField.continuous_adeleExtension ..) (fun x => ?_)
      (fun a h1 h0 => ?_)
    · apply (adeleRingEquiv L).injective
      simp only [f, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
        adeleRingEquiv_algebraMap, NumberField.adeleExtension_algebraMap]
      exact adeleMap_diag x
    · obtain ⟨a1, a2⟩ := a
      simp only at h1 h0
      subst h1 h0
      refine Prod.ext ?_ ?_
      · change (InfiniteAdeleRing.ringEquiv_mixedSpace L).symm (infRingHom K L (InfiniteAdeleRing.ringEquiv_mixedSpace K 1)) =
          NumberField.infiniteAdeleExtension K L 1
        rw [map_one, map_one, map_one, map_one]
      · change finMap K L 0 = IsDedekindDomain.finiteAdeleExtension (𝓞 K) K (𝓞 L) L 0
        simp
  rw [← h]
  exact (adeleRingEquiv L).apply_symm_apply _

end Adeles

/-! ### The comparison -/

section Comparison

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)

omit [DecidableEq ι] in
theorem adeleLmat_add (y z : Adeles L) : adeleLmat b (y + z) = adeleLmat b y + adeleLmat b z :=
  Matrix.ext fun i j => by
    simp only [adeleLmat, Matrix.of_apply, Matrix.add_apply, add_mul, map_add, Pi.add_apply]

omit [DecidableEq ι] in
theorem adeleLmat_zero : adeleLmat b 0 = 0 :=
  Matrix.ext fun i j => by
    simp only [adeleLmat, Matrix.of_apply, zero_mul, map_zero, Pi.zero_apply, Matrix.zero_apply]

/-- $M\big(\sum_ib_i\,\iota(a_i)\big) = \sum_ia_i\,M_b(b_i)$. -/
theorem adeleLmat_adeleBaseChange (a : AdeleSpace K ι) :
    adeleLmat b (adeleBaseChange b a) =
      ∑ i, Matrix.scalar ι (a i) * (Algebra.leftMulMatrix b (b i)).map (diagRing K) := by
  let F : Adeles L →+ Matrix ι ι (Adeles K) :=
    { toFun := adeleLmat b, map_zero' := adeleLmat_zero b, map_add' := adeleLmat_add b }
  rw [adeleBaseChange_apply]
  change F _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change adeleLmat b _ = _
  rw [adeleLmat_mul, adeleLmat_diag, adeleLmat_adeleMap]
  exact (Matrix.scalar_commute (a i) (fun r => Commute.all _ r) _).eq.symm

theorem det_adeleLmat_adeleBaseChange (a : AdeleSpace K ι) :
    (adeleLmat b (adeleBaseChange b a)).det = normForm b (diagRing K) a := by
  rw [adeleLmat_adeleBaseChange, normForm]

/-- At an infinite place $v$ of $K$: $\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}\big((\sum_ib_i\,\iota(c_i))_w\big) =
\det(\sum_ic_{i,v}M_b(b_i))$. -/
theorem finprod_norm_infinite (v : InfinitePlace K) (c : ι → InfiniteAdeleRing K) :
    ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
      Algebra.norm v.Completion
        ((∑ i, algebraMap L (InfiniteAdeleRing L) (b i) * NumberField.infiniteAdeleExtension K L (c i)) w.1) =
      normForm b (algebraMap K v.Completion) (fun i => c i v) := by
  classical
  rw [finprod_eq_prod_of_fintype, ← norm_sum_tmul,
    ← Algebra.norm_eq_of_algEquiv (TauCeti.GlobalNumberFields.infiniteSemilocalEquiv L v), TauCeti.Algebra.norm_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [map_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TauCeti.GlobalNumberFields.infiniteSemilocalEquiv_tmul]
  obtain ⟨w, hw⟩ := w
  obtain rfl : w.comap (algebraMap K L) = v := InfinitePlace.LiesOver.comap_eq w v
  rw [Pi.mul_apply, NumberField.infiniteAdeleExtension_apply, InfiniteAdeleRing.algebraMap_apply, mul_comm]
  rfl

/-- At a finite place $v$ of $K$: $\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}\big((\sum_ib_i\,\iota(c_i))_w\big) =
\det(\sum_ic_{i,v}M_b(b_i))$. -/
theorem finprod_norm_finite (v : HeightOneSpectrum (𝓞 K)) (c : ι → FiniteAdeleRing (𝓞 K) K) :
    ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.norm (v.adicCompletion K)
        ((∑ i, algebraMap L (FiniteAdeleRing (𝓞 L) L) (b i) *
          IsDedekindDomain.finiteAdeleExtension (𝓞 K) K (𝓞 L) L (c i)) w.1) =
      normForm b (algebraMap K (v.adicCompletion K)) (fun i => c i v) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype, ← norm_sum_tmul, TauCeti.norm_eq_prod_norm_semilocalEquiv]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  have hsum : ∀ (f : ι → FiniteAdeleRing (𝓞 L) L) (u : HeightOneSpectrum (𝓞 L)),
      (∑ i, f i) u = ∑ i, f i u := fun f u =>
    map_sum (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 L) => u.adicCompletion L) u) f
      Finset.univ
  rw [map_sum, Finset.sum_apply, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TauCeti.semilocalEquiv_tmul]
  change (algebraMap L (FiniteAdeleRing (𝓞 L) L) (b i)) w.1 *
    (IsDedekindDomain.finiteAdeleExtension (𝓞 K) K (𝓞 L) L (c i)) w.1 = _
  obtain ⟨w, hw⟩ := w
  obtain rfl : w.under (𝓞 K) = v := HeightOneSpectrum.ext hw.over.symm
  rw [IsDedekindDomain.finiteAdeleExtension_apply, ← HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra,
    FiniteAdeleRing.algebraMap_apply, mul_comm]
  rfl

/-- **Our relative idele norm is Tau Ceti's**: `ideleRelNorm b x = TauCeti.GlobalNumberFields.ideleNormMap K L x`
for every idele $x$ of $L$ and every $K$-basis $b$ of $L$. -/
@[kb "milne2020cft" "Ch. V, §4, p. 177 (the norm of idèles; comparison of two constructions)"]
theorem ideleRelNorm_eq_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    ideleRelNorm b x = TauCeti.GlobalNumberFields.ideleNormMap K L x := by
  apply Units.ext
  set Y : Adeles L := adeleRingEquiv L (x : AdeleRing (𝓞 L) L) with hYdef
  set a : AdeleSpace K ι := (adeleBaseChange b).symm Y with hadef
  set a' : ι → AdeleRing (𝓞 K) K := fun i => (adeleRingEquiv K).symm (a i) with ha'def
  have hY : (x : AdeleRing (𝓞 L) L) =
      ∑ i, algebraMap L (AdeleRing (𝓞 L) L) (b i) * NumberField.adeleExtension (𝓞 K) K (𝓞 L) L (a' i) := by
    apply (adeleRingEquiv L).injective
    rw [map_sum]
    simp_rw [map_mul, adeleRingEquiv_algebraMap, adeleRingEquiv_adeleExtension, ha'def,
      RingEquiv.apply_symm_apply]
    rw [← adeleBaseChange_apply, hadef, (adeleBaseChange b).apply_symm_apply]
  have hcomp : ((adeleRingEquiv K).symm : Adeles K →+* AdeleRing (𝓞 K) K).comp (diagRing K) =
      algebraMap K (AdeleRing (𝓞 K) K) := by
    ext ξ
    rw [RingHom.comp_apply, ← adeleRingEquiv_algebraMap]
    exact (adeleRingEquiv K).symm_apply_apply _
  have hL : ((ideleRelNorm b x : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) =
      normForm b (algebraMap K (AdeleRing (𝓞 K) K)) a' := by
    change (adeleRingEquiv K).symm (adeleLmat b Y).det = _
    rw [← (adeleBaseChange b).apply_symm_apply Y, ← hadef, det_adeleLmat_adeleBaseChange]
    change ((adeleRingEquiv K).symm : Adeles K →+* AdeleRing (𝓞 K) K) _ = _
    rw [map_normForm, hcomp]
    rfl
  rw [hL, TauCeti.GlobalNumberFields.coe_ideleNormMap, hY]
  refine Prod.ext ?_ ?_
  · funext v
    rw [TauCeti.GlobalNumberFields.adeleNorm_fst, TauCeti.GlobalNumberFields.infiniteAdeleNorm_apply]
    have h1 : (∑ i, algebraMap L (AdeleRing (𝓞 L) L) (b i) *
        NumberField.adeleExtension (𝓞 K) K (𝓞 L) L (a' i)).1 =
        ∑ i, algebraMap L (InfiniteAdeleRing L) (b i) * NumberField.infiniteAdeleExtension K L (a' i).1 := by
      rw [Prod.fst_sum]
      rfl
    rw [h1, finprod_norm_infinite]
    let ψ : AdeleRing (𝓞 K) K →+* v.Completion :=
      (Pi.evalRingHom _ v).comp (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
    exact map_normForm b _ ψ a'
  · refine FiniteAdeleRing.ext K fun v => ?_
    rw [TauCeti.GlobalNumberFields.adeleNorm_snd, TauCeti.GlobalNumberFields.finiteAdeleNorm_apply]
    have h2 : (∑ i, algebraMap L (AdeleRing (𝓞 L) L) (b i) *
        NumberField.adeleExtension (𝓞 K) K (𝓞 L) L (a' i)).2 =
        ∑ i, algebraMap L (FiniteAdeleRing (𝓞 L) L) (b i) *
          IsDedekindDomain.finiteAdeleExtension (𝓞 K) K (𝓞 L) L (a' i).2 := by
      rw [Prod.snd_sum]
      rfl
    rw [h2, finprod_norm_finite]
    let ψ : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
      (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v).comp
        (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
    exact map_normForm b _ ψ a'

end Comparison

end

end NumberFieldKB.Ideles
