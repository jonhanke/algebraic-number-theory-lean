import NumberFieldKB.MilneEC.LocalPoints

/-!
# Algebraic points of $E(K_v)$

`IsAlgPoint W Kv T`: the coordinates of $T \in E(K_v)$ are algebraic over $K$. `isAlgPoint_iff` identifies this
with the condition in `KummerApprox` (the image of $T$ in $E(\bar K_v)$ comes from $E(\bar K)$), so
`kummerApprox_iff` restates `KummerApprox` intrinsically and `kummerApprox_of_algEquiv` transports it along
$K$-algebra isomorphisms $K_v \cong K_v'$ (used to pass from the completion of $\mathbb Q$ at the real place to
$\mathbb R$).
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace NumberFieldKB.MilneEC

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (Kv : Type) [Field Kv] [Algebra K Kv]

/-- A point of $E(K_v)$ whose coordinates are algebraic over $K$. -/
def IsAlgPoint : (W.toAffine⁄Kv).Point → Prop
  | .zero => True
  | .some x y _ => IsAlgebraic K x ∧ IsAlgebraic K y

omit [DecidableEq K] in
theorem isAlgPoint_zero : IsAlgPoint W Kv 0 := trivial

/-- A point of $E(K_v)$ is algebraic iff its image in $E(\bar K_v)$ comes from $E(\bar K)$. -/
theorem isAlgPoint_iff (T : (W.toAffine⁄Kv).Point) :
    IsAlgPoint W Kv T ↔
      inclPoints W Kv T ∈ Set.range (Point.map (W' := W.toAffine) (closureEmb (K := K) Kv)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv)) :=
    (algebraMap Kv (AlgebraicClosure Kv)).injective
  rcases T with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => ⟨0, map_zero _⟩, fun _ => trivial⟩
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : IsAlgebraic K (algebraMap Kv (AlgebraicClosure Kv) x) :=
      hx.algHom (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv))
    have hy' : IsAlgebraic K (algebraMap Kv (AlgebraicClosure Kv) y) :=
      hy.algHom (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv))
    obtain ⟨x₀, hx₀⟩ := mem_range_closureEmb_of_isAlgebraic Kv hx'
    obtain ⟨y₀, hy₀⟩ := mem_range_closureEmb_of_isAlgebraic Kv hy'
    have h' : (W.toAffine⁄(AlgebraicClosure Kv)).Nonsingular (closureEmb Kv x₀) (closureEmb Kv y₀) := by
      rw [hx₀, hy₀]
      exact (W.toAffine.baseChange_nonsingular hinj x y).2 h
    have h₀ : (W.toAffine⁄(AlgebraicClosure K)).Nonsingular x₀ y₀ :=
      (W.toAffine.baseChange_nonsingular (closureEmb Kv).injective x₀ y₀).1 h'
    refine ⟨.some _ _ h₀, ?_⟩
    simp only [Point.map_some, Point.some.injEq]
    exact ⟨hx₀, hy₀⟩
  · rintro ⟨U, hU⟩
    rcases U with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hU (by rintro ⟨⟩)
    simp only [Point.map_some, Point.some.injEq] at hU
    have hx : IsAlgebraic K (closureEmb Kv x₀) := (Algebra.IsAlgebraic.isAlgebraic x₀).algHom _
    have hy : IsAlgebraic K (closureEmb Kv y₀) := (Algebra.IsAlgebraic.isAlgebraic y₀).algHom _
    rw [hU.1] at hx
    rw [hU.2] at hy
    exact ⟨(isAlgebraic_algHom_iff _ hinj).1 hx, (isAlgebraic_algHom_iff _ hinj).1 hy⟩

/-- `KummerApprox`, intrinsically: every point is $nS + T$ with $T$ algebraic. -/
theorem kummerApprox_iff (n : ℕ) :
    KummerApprox W Kv n ↔ ∀ R : (W.toAffine⁄Kv).Point, ∃ S T, IsAlgPoint W Kv T ∧ R = n • S + T := by
  constructor
  · intro h R
    obtain ⟨S, T, hR⟩ := h R
    refine ⟨S, R - n • S, (isAlgPoint_iff W Kv _).2 ⟨T, ?_⟩, by abel⟩
    rw [map_sub, hR, map_nsmul]
    abel
  · intro h R
    obtain ⟨S, T, hT, hR⟩ := h R
    obtain ⟨U, hU⟩ := (isAlgPoint_iff W Kv T).1 hT
    exact ⟨S, U, by rw [hU, hR, map_add, map_nsmul]⟩

variable {Kv} {Kv' : Type} [Field Kv'] [Algebra K Kv']

omit [DecidableEq K] in
/-- `IsAlgPoint` is preserved by a $K$-algebra isomorphism. -/
theorem isAlgPoint_map (e : Kv ≃ₐ[K] Kv') (T : (W.toAffine⁄Kv).Point) :
    IsAlgPoint W Kv' (Point.map (W' := W.toAffine) (e : Kv →ₐ[K] Kv') T) ↔ IsAlgPoint W Kv T := by
  rcases T with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => trivial, fun _ => trivial⟩
  simp only [Point.map_some]
  exact and_congr (isAlgebraic_algHom_iff _ e.injective) (isAlgebraic_algHom_iff _ e.injective)

omit [DecidableEq K] in
theorem map_map_symm (e : Kv ≃ₐ[K] Kv') (T : (W.toAffine⁄Kv').Point) :
    Point.map (W' := W.toAffine) (e : Kv →ₐ[K] Kv') (Point.map (W' := W.toAffine) (e.symm : Kv' →ₐ[K] Kv) T) =
      T := by
  rw [Point.map_map]
  have : (e : Kv →ₐ[K] Kv').comp (e.symm : Kv' →ₐ[K] Kv) = AlgHom.id K Kv' :=
    AlgHom.ext fun a => e.apply_symm_apply a
  rw [this]
  exact Point.map_id T

/-- **Transport of `KummerApprox`** along a $K$-algebra isomorphism $K_v \cong K_v'$. -/
theorem kummerApprox_of_algEquiv (e : Kv ≃ₐ[K] Kv') (n : ℕ) (h : KummerApprox W Kv' n) :
    KummerApprox W Kv n := by
  rw [kummerApprox_iff] at h ⊢
  intro R
  obtain ⟨S, T, hT, hR⟩ := h (Point.map (W' := W.toAffine) (e : Kv →ₐ[K] Kv') R)
  refine ⟨Point.map (W' := W.toAffine) (e.symm : Kv' →ₐ[K] Kv) S,
    Point.map (W' := W.toAffine) (e.symm : Kv' →ₐ[K] Kv) T, ?_, ?_⟩
  · rw [← isAlgPoint_map W e, map_map_symm]
    exact hT
  · rw [← map_nsmul, ← map_add, ← hR]
    exact (map_map_symm W e.symm R).symm

end NumberFieldKB.MilneEC
