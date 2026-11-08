import Mathlib

/-!
# Milne, *Algebraic Number Theory*, p. 82: auxiliary results for the norm form of an ideal basis

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 82; bib key `milne2020ant`.

For a quadratic field $K$ (no conjugation needed): Cayley–Hamilton $u^2 = \mathrm{Tr}(u)u - \mathrm{N}(u)$, the
expansion $\mathrm{N}(ux + vy) = \mathrm{N}(u)x^2 + (\mathrm{Tr}\,u\,\mathrm{Tr}\,v - \mathrm{Tr}(uv))xy +
\mathrm{N}(v)y^2$, the identity relating the discriminant of this binary form to $\det(\mathrm{Tr}(b_ib_j))$,
$D(b_0, b_1) = N\mathfrak a^2\,d_K$ for a $\mathbb Z$-basis of a fractional ideal, and
$N\mathfrak a \mid \mathrm{N}(x)$ for $x \in \mathfrak a$. Used by `NumberFieldKB.MilneANT.idealNormForm_integral`
in `Ch4.lean`.
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors Matrix

namespace NumberFieldKB.MilneANT.NormForm

section quad

variable {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]

theorem quad_cayley (hK : finrank ℚ K = 2) (u : K) :
    u * u = algebraMap ℚ K (Algebra.trace ℚ K u) * u - algebraMap ℚ K (Algebra.norm ℚ u) := by
  let bs : Basis (Fin 2) ℚ K := Module.finBasisOfFinrankEq ℚ K hK
  have h := Matrix.aeval_self_charpoly (Algebra.leftMulMatrix bs u)
  rw [Matrix.charpoly_fin_two] at h
  have ht := Algebra.trace_eq_matrix_trace bs u
  have hn := Algebra.norm_eq_matrix_det bs u
  apply Algebra.leftMulMatrix_injective bs
  simp only [map_mul, map_sub, map_smul, Algebra.algebraMap_eq_smul_one, map_one]
  simp at h
  rw [ht, hn]
  simp only [Algebra.algebraMap_eq_smul_one] at h
  rw [pow_two, smul_mul_assoc, one_mul] at h
  rw [smul_mul_assoc, one_mul]
  rw [← sub_eq_zero, ← h]
  abel

theorem trace_algebraMap_mul (q : ℚ) (w : K) :
    Algebra.trace ℚ K (algebraMap ℚ K q * w) = q * Algebra.trace ℚ K w := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem quad_polar (hK : finrank ℚ K = 2) (u v : K) :
    2 * (u * v) = algebraMap ℚ K (Algebra.trace ℚ K v) * u + algebraMap ℚ K (Algebra.trace ℚ K u) * v
      - algebraMap ℚ K (Algebra.norm ℚ (u + v) - Algebra.norm ℚ u - Algebra.norm ℚ v) := by
  have h1 := quad_cayley hK (u + v)
  have h2 := quad_cayley hK u
  have h3 := quad_cayley hK v
  rw [map_add (Algebra.trace ℚ K), map_add] at h1
  simp only [map_sub, map_add] 
  linear_combination h1 - h2 - h3

theorem quad_trace_mul (hK : finrank ℚ K = 2) (u v : K) :
    Algebra.trace ℚ K (u * v) = Algebra.trace ℚ K u * Algebra.trace ℚ K v
      - (Algebra.norm ℚ (u + v) - Algebra.norm ℚ u - Algebra.norm ℚ v) := by
  have h := congrArg (Algebra.trace ℚ K) (quad_polar hK u v)
  have h2 : Algebra.trace ℚ K (2 * (u * v)) = 2 * Algebra.trace ℚ K (u * v) := by
    have := trace_algebraMap_mul (K := K) 2 (u * v)
    simpa using this
  rw [h2, map_sub, map_add, trace_algebraMap_mul, trace_algebraMap_mul, Algebra.trace_algebraMap, hK] at h
  simp at h
  linarith

omit [Algebra ℚ K] [FiniteDimensional ℚ K] in
theorem quad_ring_rel {R : Type*} [CommRing R] (u v tu tv nu nv p : R)
    (e1 : u * u = tu * u - nu) (e2 : v * v = tv * v - nv)
    (e3 : 2 * (u * v) = tv * u + tu * v - p) :
    (-2 * p * tv + 4 * tu * nv) * u + (-2 * p * tu + 4 * nu * tv) * v
      + (p ^ 2 + tu * tv * p - tv ^ 2 * nu - tu ^ 2 * nv - 4 * nu * nv) = 0 := by
  linear_combination (4 * (v * v) - tv ^ 2) * e1 + (4 * (tu * u - nu) - tu ^ 2) * e2
    + (-((tv * u + tu * v - p) + 2 * (u * v)) + tu * tv) * e3

theorem quad_trace_sq (hK : finrank ℚ K = 2) (u : K) :
    Algebra.trace ℚ K (u * u) = Algebra.trace ℚ K u ^ 2 - 2 * Algebra.norm ℚ u := by
  have h := congrArg (Algebra.trace ℚ K) (quad_cayley hK u)
  rw [map_sub, trace_algebraMap_mul, Algebra.trace_algebraMap, hK] at h
  rw [h]; simp; ring

theorem quad_disc_id (hK : finrank ℚ K = 2) (u v : K) :
    (Algebra.norm ℚ (u + v) - Algebra.norm ℚ u - Algebra.norm ℚ v) ^ 2
      - 4 * Algebra.norm ℚ u * Algebra.norm ℚ v =
    Algebra.trace ℚ K (u * u) * Algebra.trace ℚ K (v * v) - Algebra.trace ℚ K (u * v) ^ 2 := by
  set tu := Algebra.trace ℚ K u
  set tv := Algebra.trace ℚ K v
  set nu := Algebra.norm ℚ u
  set nv := Algebra.norm ℚ v
  set p := Algebra.norm ℚ (u + v) - nu - nv with hp
  have E := quad_ring_rel u v (algebraMap ℚ K tu) (algebraMap ℚ K tv) (algebraMap ℚ K nu)
    (algebraMap ℚ K nv) (algebraMap ℚ K p) (quad_cayley hK u) (quad_cayley hK v) (quad_polar hK u v)
  have E' : algebraMap ℚ K (-2 * p * tv + 4 * tu * nv) * u + algebraMap ℚ K (-2 * p * tu + 4 * nu * tv) * v
      + algebraMap ℚ K (p ^ 2 + tu * tv * p - tv ^ 2 * nu - tu ^ 2 * nv - 4 * nu * nv) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    exact E
  have h := congrArg (Algebra.trace ℚ K) E'
  rw [map_add, map_add, trace_algebraMap_mul, trace_algebraMap_mul, Algebra.trace_algebraMap, hK,
    map_zero] at h
  rw [quad_trace_sq hK, quad_trace_sq hK, quad_trace_mul hK]
  simp only [nsmul_eq_mul, hp, tu, tv, nu, nv] at h ⊢
  push_cast at h
  linear_combination h

end quad

section nf

variable {K : Type*} [Field K] [NumberField K]

theorem discr_frac (hK : finrank ℚ K = 2) (a : FractionalIdeal (𝓞 K)⁰ K)
    (b : Basis (Fin 2) ℤ (a : Submodule (𝓞 K) K)) :
    Algebra.discr ℚ (fun i => (b i : K)) = (FractionalIdeal.absNorm a) ^ 2 * (discr K : ℚ) := by
  have hr : finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  let ω : Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hr
  let b₀ : Basis (Fin 2) ℚ K := ω.localizationLocalization ℚ ℤ⁰ K
  have h1 := FractionalIdeal.abs_det_basis_change ω a b
  have h2 : (fun i => (b i : K)) = b₀ ᵥ* ((b₀.toMatrix (fun i => (b i : K))).map (algebraMap ℚ K)) :=
    (Basis.toMatrix_map_vecMul b₀ _).symm
  have h3 := Algebra.discr_of_matrix_vecMul (A := ℚ) (b₀ : Fin 2 → K) (b₀.toMatrix (fun i => (b i : K)))
  have h4 : Algebra.discr ℚ (b₀ : Fin 2 → K) = (discr K : ℚ) := by
    rw [← NumberField.discr_eq_discr K ω]
    simpa using Algebra.discr_localizationLocalization (Rₘ := ℚ) ℤ ℤ⁰ K ω
  rw [← h2, h4] at h3
  rw [h3, ← h1, sq_abs, Basis.det_apply]
  rfl

theorem norm_div_absNorm_int (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : K)
    (hx : x ∈ (a : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ z : ℤ, Algebra.norm ℚ x = FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) * z := by
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ (a : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 hx
  have hc : ((a⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ 1 := by
    calc _ ≤ ((a⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) * (a : FractionalIdeal (𝓞 K)⁰ K) :=
          mul_le_mul_right hle _
      _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = (a : FractionalIdeal (𝓞 K)⁰ K) * I := by
    rw [hI, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hn := congrArg FractionalIdeal.absNorm hs
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm] at hn
  rcases abs_cases (Algebra.norm ℚ x) with ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨(Ideal.absNorm I : ℤ), by rw [← h, hn]; simp⟩
  · exact ⟨-(Ideal.absNorm I : ℤ), by
      have : Algebra.norm ℚ x = -(|Algebra.norm ℚ x|) := by linarith
      rw [this, hn]; simp⟩

theorem norm_expand (hK : finrank ℚ K = 2) (u v : K) (x y : ℚ) :
    Algebra.norm ℚ (u * (x : K) + v * (y : K)) =
      Algebra.norm ℚ u * x ^ 2 + Algebra.norm ℚ v * y ^ 2
        + (Algebra.trace ℚ K u * Algebra.trace ℚ K v - Algebra.trace ℚ K (u * v)) * (x * y) := by
  have hx : (x : K) = algebraMap ℚ K x := (eq_ratCast _ _).symm
  have hy : (y : K) = algebraMap ℚ K y := (eq_ratCast _ _).symm
  have e1 : u * (x : K) = algebraMap ℚ K x * u := by rw [hx, mul_comm, Algebra.commutes]
  have e2 : v * (y : K) = algebraMap ℚ K y * v := by rw [hy, mul_comm, Algebra.commutes]
  have key := quad_trace_mul hK (algebraMap ℚ K x * u) (algebraMap ℚ K y * v)
  have hUV : algebraMap ℚ K x * u * (algebraMap ℚ K y * v) = algebraMap ℚ K (x * y) * (u * v) := by
    rw [map_mul]; ring
  rw [hUV, trace_algebraMap_mul, trace_algebraMap_mul, trace_algebraMap_mul] at key
  rw [e1, e2]
  have n1 : Algebra.norm ℚ (algebraMap ℚ K x * u) = x ^ 2 * Algebra.norm ℚ u := by
    rw [map_mul, Algebra.norm_algebraMap, hK]
  have n2 : Algebra.norm ℚ (algebraMap ℚ K y * v) = y ^ 2 * Algebra.norm ℚ v := by
    rw [map_mul, Algebra.norm_algebraMap, hK]
  rw [n1, n2] at key
  linear_combination key

end nf

end NumberFieldKB.MilneANT.NormForm
