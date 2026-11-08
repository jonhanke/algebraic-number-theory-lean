import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# Weil, *Basic Number Theory*, Chapter IV, §3, Proposition 3, for $E=k^n$

$k$ is a number field, $E=k^n$ (coordinates indexed by a finite type `ι`), so $\mathrm{End}(E)_{\mathbb A}$ is the ring of
$n\times n$ matrices over the adeles $k_{\mathbb A}$ (QuadFormsKB's `Adeles k` $=k_\infty\times\mathbb A_f$) and
$E_{\mathbb A}=k_{\mathbb A}^n$.

**Prop. 3** (p. 73): for $a\in\mathrm{End}(E)_{\mathbb A}$ the following are equivalent: (i) $a$ is an idele of
$\mathrm{End}(E)$ (a unit); (ii) $\det a$ is an idele of $k$; (iii) $e\mapsto ae$ is an automorphism of $E_{\mathbb A}$.
When that is so, the module of $e\mapsto ae$ is $\lvert\det a\rvert_{\mathbb A}$, and $\det$ is a continuous morphism.

* **`weil_IV_3_prop3_iff`**: (i) $\iff$ (ii) $\iff$ ($e\mapsto ae$ is bijective) (Mathlib `Matrix.isUnit_iff_isUnit_det`,
  `Matrix.mulVec_surjective_iff_isUnit`); a bijective $k_{\mathbb A}$-linear map of $k_{\mathbb A}^n$ given by a unit
  matrix is a homeomorphism, its inverse being the inverse matrix;
* **`weil_IV_3_prop3_module`**: for $a\in\mathrm{GL}_n(k_{\mathbb A})$, $a_*\mu=\lvert\det a\rvert_{\mathbb A}^{-1}\mu$ for
  the Haar measure $\mu$ of $k_{\mathbb A}^n$, i.e. the module of $e\mapsto ae$ is $\lvert\det a\rvert_{\mathbb A}$
  (QuadFormsKB `map_mulVec_muAddVec`; $\lvert\cdot\rvert_{\mathbb A}$ = `ideleNorm`);
* **`weil_IV_3_prop3_continuous_det`**: $\det$ is continuous on $\mathrm{End}(E)_{\mathbb A}$.

Weil's general $E$ and the corollary for algebras are not packaged here.
-/

open IsDedekindDomain NumberField MeasureTheory QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Weil, IV.§3, Prop. 3** ($E=k^n$), the equivalences: an adelic matrix $a$ is a unit iff $\det a$ is an idele iff
$e\mapsto ae$ is a bijection of $k_{\mathbb A}^n$. -/
@[kb "weil1973bnt" "Ch. IV, §3, Prop. 3 (p. 73), E = k^n, equivalence of (i)-(iii), number field case"]
theorem weil_IV_3_prop3_iff (a : Matrix ι ι (Adeles F)) :
    (IsUnit a ↔ IsUnit a.det) ∧ (IsUnit a ↔ Function.Bijective a.mulVec) := by
  refine ⟨Matrix.isUnit_iff_isUnit_det a, ⟨fun h => ⟨?_, Matrix.mulVec_surjective_iff_isUnit.mpr h⟩,
    fun h => Matrix.mulVec_surjective_iff_isUnit.mp h.2⟩⟩
  obtain ⟨u, rfl⟩ := h
  intro x y hxy
  have := congrArg (Matrix.mulVec ((u⁻¹ : (Matrix ι ι (Adeles F))ˣ) : Matrix ι ι (Adeles F))) hxy
  simpa [Matrix.mulVec_mulVec] using this

/-- **Weil, IV.§3, Prop. 3** ($E=k^n$), the module: for $a\in\mathrm{GL}_n(k_{\mathbb A})$, the image of the Haar measure
$\mu$ of $k_{\mathbb A}^n$ under $e\mapsto ae$ is $\lvert\det a\rvert_{\mathbb A}^{-1}\mu$. -/
@[kb "weil1973bnt" "Ch. IV, §3, Prop. 3 (p. 73), E = k^n, the module |det a|_A, number field case"]
theorem weil_IV_3_prop3_module (a : GL ι (Adeles F)) :
    Measure.map (a : Matrix ι ι (Adeles F)).mulVec (muAddVec F ι) =
      ENNReal.ofReal (ideleNorm F (Matrix.GeneralLinearGroup.det a))⁻¹ • muAddVec F ι :=
  map_mulVec_muAddVec a

/-- **Weil, IV.§3, Prop. 3**: $\det$ is continuous on $\mathrm{End}(E)_{\mathbb A}$. -/
theorem weil_IV_3_prop3_continuous_det : Continuous fun a : Matrix ι ι (Adeles F) => a.det :=
  continuous_id.matrix_det

end NumberFieldKB.WeilBNT
