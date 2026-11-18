import NumberFieldKB.MilneEC.ShaComparison
import NumberFieldKB.MilneEC.Ch4Lemma21

/-!
# Local injectivity from Kummer approximation

`LocalPointsInjectiveAt W Kv` (`ShaComparison.lean`) asks that a continuous crossed homomorphism $c$ of
$G_v = \operatorname{Gal}(\bar K_v/K_v)$ into $E(\bar K)$ whose image in $E(\bar K_v)$ is principal be principal.
This file reduces it, for $K_v$ of characteristic $0$, to a statement about points over $K_v$ alone:

* `KummerApprox W Kv n`: every point of $E(K_v)$ is $n S + T$ with $S \in E(K_v)$ and $T$ a point with algebraic
  coordinates (in the image of $E(\bar K) \to E(\bar K_v)$). Equivalently, $E(K_v) \cap E(\bar K)$ maps onto
  $E(K_v)/nE(K_v)$.

**The argument** (the Kummer-theory proof of Milne, *Arithmetic Duality Theorems*, Remark I.3.10, written with
points instead of $H^1(\,\cdot\,, E_n)$):

1. `exists_nsmul_eq_coboundary`: a continuous crossed homomorphism of a compact group into a discrete module has a
   principal multiple $n c$, $n \ge 1$ (its zero set is an open subgroup of finite index $n$).
2. If $\iota c(\sigma) = \sigma Q - Q$ with $Q \in E(\bar K_v)$ and $n c(\sigma) = \sigma P - P$, then
   $nQ - \iota P$ is fixed by $G_v$, so it is a point $R$ of $E(K_v)$ (`exists_of_forall_fixed`).
3. Write $R = nS + \iota T$ (`KummerApprox`). Then $n(Q - S) = \iota(P + T)$, and $Q - S = \iota U$ is itself
   algebraic (`exists_closureEmb_of_nsmul`: divisibility of $E(\bar K)$, `lemma2_1`, and algebraicity of torsion
   points of $E(\bar K_v)$, `exists_closureEmb_of_torsion`).
4. Then $\iota c(\sigma) = \sigma(\iota U) - \iota U$, and $c$ is principal since $\iota$ is injective.

## Main results
* `localPointsInjectiveAt_of_kummerApprox`: `KummerApprox W Kv n` for every $n \ge 1$ implies
  `LocalPointsInjectiveAt W Kv`.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Classical

namespace NumberFieldKB.MilneEC

/-! ## Continuous crossed homomorphisms of compact groups are torsion classes -/

section Torsion

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The zero set of a crossed homomorphism is a subgroup. -/
def cocycleKer {A : Rep.{0} ℤ G} (c : cocycles₁ A) : Subgroup G where
  carrier := {g | c g = 0}
  one_mem' := by
    have h := (mem_cocycles₁_iff (c : G → A)).1 c.2 1 1
    simp only [one_mul, map_one] at h
    change c 1 = 0
    have : (c : G → A) 1 = (c : G → A) 1 + (c : G → A) 1 := h
    exact (left_eq_add.1 this)
  mul_mem' {a b} ha hb := by
    change c (a * b) = 0
    have h := (mem_cocycles₁_iff (c : G → A)).1 c.2 a b
    change (c : G → A) a = 0 at ha
    change (c : G → A) b = 0 at hb
    change (c : G → A) (a * b) = 0
    rw [h, ha, hb, map_zero, add_zero]
  inv_mem' {a} ha := by
    change (c : G → A) a = 0 at ha
    change (c : G → A) a⁻¹ = 0
    have h := (mem_cocycles₁_iff (c : G → A)).1 c.2 a a⁻¹
    have h1 := (mem_cocycles₁_iff (c : G → A)).1 c.2 1 1
    simp only [one_mul, map_one] at h1
    have h0 : (c : G → A) 1 = 0 := left_eq_add.1 (show (c : G → A) 1 = (c : G → A) 1 + (c : G → A) 1 from h1)
    rw [mul_inv_cancel, h0, ha, add_zero] at h
    have := congrArg (A.ρ a⁻¹) h.symm
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact this

/-- A crossed homomorphism is constant on left cosets of its zero set. -/
theorem cocycle_mul_of_mem_cocycleKer {A : Rep.{0} ℤ G} (c : cocycles₁ A) (g h : G) (hh : h ∈ cocycleKer c) :
    c (g * h) = c g := by
  have h' := (mem_cocycles₁_iff (c : G → A)).1 c.2 g h
  change (c : G → A) h = 0 at hh
  change (c : G → A) (g * h) = (c : G → A) g
  rw [h', hh, map_zero, zero_add]

/-- **A continuous crossed homomorphism into a discrete module has a principal multiple**: if $c$ is continuous for
the discrete topology on $A$ and $G$ is compact, then $n c(g) = g m - m$ for some $n \ge 1$ and $m \in A$. -/
theorem exists_nsmul_eq_coboundary (A : Rep.{0} ℤ G) (c : cocycles₁ A) (hc : @Continuous G A _ ⊥ c) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : A, ∀ g, n • c g = A.ρ g m - m := by
  let H := cocycleKer c
  have hopen : IsOpen (H : Set G) := by
    letI : TopologicalSpace A := ⊥
    have : DiscreteTopology A := ⟨rfl⟩
    exact (isOpen_discrete ({0} : Set A)).preimage hc
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let f : G ⧸ H → A := fun q => c q.out
  have hf : ∀ g : G, f (QuotientGroup.mk g) = c g := fun g => by
    obtain ⟨h, hh, he⟩ : ∃ h ∈ H, (QuotientGroup.mk g : G ⧸ H).out = g * h := by
      refine ⟨g⁻¹ * (QuotientGroup.mk g : G ⧸ H).out, ?_, by group⟩
      exact QuotientGroup.leftRel_apply.1 (Quotient.exact (Quotient.out_eq _).symm)
    change c (QuotientGroup.mk g : G ⧸ H).out = c g
    rw [he, cocycle_mul_of_mem_cocycleKer c g h hh]
  refine ⟨Fintype.card (G ⧸ H), Fintype.card_pos, -∑ q, f q, fun g => ?_⟩
  have hsum : ∑ q, f (g • q) = ∑ q, f q :=
    Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  have hterm : ∀ q : G ⧸ H, A.ρ g (f q) = f (g • q) - c g := fun q => by
    have h1 := (mem_cocycles₁_iff (c : G → A)).1 c.2 g q.out
    have h2 : f (g • q) = c (g * q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      exact hf (g * q.out)
    rw [h2]
    change A.ρ g ((c : G → A) q.out) = (c : G → A) (g * q.out) - (c : G → A) g
    rw [h1]
    abel
  rw [map_neg, map_sum]
  simp only [hterm, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ]
  abel

end Torsion

/-! ## Points of $E(\bar K_v)$ with algebraic coordinates -/

section Algebraic

variable {K : Type} [Field K] [DecidableEq K] (Kv : Type) [Field Kv] [Algebra K Kv]

/-- An element of $\bar K_v$ algebraic over $K$ lies in the image of $\bar K$ (`closureEmb`). -/
theorem mem_range_closureEmb_of_isAlgebraic {z : AlgebraicClosure Kv} (hz : IsAlgebraic K z) :
    z ∈ Set.range (closureEmb (K := K) Kv) := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure Kv) := (closureEmb Kv).toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq fun x => ((closureEmb Kv).commutes x).symm
  have hi : IsIntegral (AlgebraicClosure K) z := (hz.tower_top (AlgebraicClosure K)).isIntegral
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible (AlgebraicClosure K) (minpoly.irreducible hi)
  have hq : (minpoly (AlgebraicClosure K) z).leadingCoeff = 1 := minpoly.monic hi
  have : aeval z (minpoly (AlgebraicClosure K) z) = 0 := minpoly.aeval _ z
  rw [eq_X_add_C_of_degree_eq_one h1, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact ⟨-(minpoly (AlgebraicClosure K) z).coeff 0, by rw [map_neg]; exact this.symm⟩

variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Torsion points of $E(\bar K_v)$ are algebraic**: they lie in the image of $E(\bar K)$. The $x$-coordinate of
an $n$-torsion point is a root of $\Psi_n^2$, a nonzero polynomial over $K$; the $y$-coordinate is then integral over
$K$. -/
theorem exists_closureEmb_of_torsion (Q : (W.toAffine⁄(AlgebraicClosure Kv)).Point) (n : ℕ) (hn : 0 < n)
    (hQ : n • Q = 0) :
    ∃ P : (W.toAffine⁄(AlgebraicClosure K)).Point, Point.map (W' := W.toAffine) (closureEmb Kv) P = Q := by
  rcases Q with _ | ⟨x, y, hns⟩
  · exact ⟨0, map_zero _⟩
  have hΨ : ((W.baseChange (AlgebraicClosure Kv)).ΨSq n).eval x = 0 :=
    (eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns n).2 (zsmul_fromAffine_eq_zero_iff.2 (by exact_mod_cast hQ))
  rw [WeierstrassCurve.baseChange, map_ΨSq] at hΨ
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have halg : IsAlgebraic K x :=
    ⟨W.ΨSq n, W.ΨSq_ne_zero_of_Δ_ne_zero W.isUnit_Δ.ne_zero hn0, by
      rwa [aeval_def, eval₂_eq_eval_map]⟩
  have hyint : IsIntegral K y :=
    WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x W hns.1 halg.isIntegral
  obtain ⟨x₀, rfl⟩ := mem_range_closureEmb_of_isAlgebraic Kv halg
  obtain ⟨y₀, rfl⟩ := mem_range_closureEmb_of_isAlgebraic Kv hyint.isAlgebraic
  have h₀ : (W.toAffine⁄(AlgebraicClosure K)).Nonsingular x₀ y₀ :=
    (W.toAffine.baseChange_nonsingular (closureEmb Kv).injective x₀ y₀).1 hns
  exact ⟨.some _ _ h₀, rfl⟩

/-- **$E(\bar K_v)/E(\bar K)$ is torsion-free**: if $nV$ is algebraic then so is $V$ (divisibility of $E(\bar K)$,
`lemma2_1`, and `exists_closureEmb_of_torsion`). -/
theorem exists_closureEmb_of_nsmul (V : (W.toAffine⁄(AlgebraicClosure Kv)).Point) (n : ℕ) (hn : 0 < n)
    (T : (W.toAffine⁄(AlgebraicClosure K)).Point) (hT : n • V = Point.map (W' := W.toAffine) (closureEmb Kv) T) :
    ∃ U : (W.toAffine⁄(AlgebraicClosure K)).Point, Point.map (W' := W.toAffine) (closureEmb Kv) U = V := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨U₀, hU₀⟩ := Lemma2_1.surjective_baseChange W lemma2_1 (AlgebraicClosure K) n hn0 T
  have hU₀' : n • U₀ = T := by
    simpa only [natCast_zsmul] using hU₀
  have htor : n • (V - Point.map (W' := W.toAffine) (closureEmb Kv) U₀) = 0 := by
    rw [nsmul_sub, hT, ← map_nsmul, hU₀', sub_self]
  obtain ⟨U₁, hU₁⟩ := exists_closureEmb_of_torsion Kv W _ n hn htor
  refine ⟨U₀ + U₁, ?_⟩
  rw [map_add, hU₁]
  abel

end Algebraic

/-! ## The reduction -/

section Reduction

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (Kv : Type) [Field Kv] [Algebra K Kv]

/-- The inclusion $E(K_v) \to E(\bar K_v)$. -/
noncomputable abbrev inclPoints : (W.toAffine⁄Kv).Point →+ (W.toAffine⁄(AlgebraicClosure Kv)).Point :=
  Point.map (W' := W.toAffine) (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv))

/-- **Kummer approximation at $K_v$ for $n$** (named statement; proved at the real place, an input at the finite
places): every point $R \in E(K_v)$ is $nS + T$ with $S \in E(K_v)$ and $T$ a point with algebraic coordinates (the
image of a point of $E(\bar K)$ under `closureEmb`). Equivalently, the points of $E(K_v)$ with coordinates algebraic
over $K$ map onto $E(K_v)/nE(K_v)$. -/
def KummerApprox (n : ℕ) : Prop :=
  ∀ R : (W.toAffine⁄Kv).Point, ∃ S : (W.toAffine⁄Kv).Point, ∃ T : (W.toAffine⁄(AlgebraicClosure K)).Point,
    inclPoints W Kv R = n • inclPoints W Kv S + Point.map (W' := W.toAffine) (closureEmb Kv) T

variable [CharZero Kv]

/-- A point of $E(\bar K_v)$ fixed by $\operatorname{Gal}(\bar K_v/K_v)$ is a point of $E(K_v)$. -/
theorem exists_inclPoints_of_forall_fixed (Q : (W.toAffine⁄(AlgebraicClosure Kv)).Point)
    (hQ : ∀ σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv, (localPointsRep Kv W).ρ σ Q = Q) :
    ∃ R : (W.toAffine⁄Kv).Point, inclPoints W Kv R = Q := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact ⟨0, map_zero _⟩
  have hx : ∀ σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv, σ x = x := fun σ => by
    have := hQ σ
    change Point.map (W' := W.toAffine) _ (Point.some x y hxy) = _ at this
    simp only [Point.map_some] at this
    exact (Point.some.inj this).1
  have hy : ∀ σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv, σ y = y := fun σ => by
    have := hQ σ
    change Point.map (W' := W.toAffine) _ (Point.some x y hxy) = _ at this
    simp only [Point.map_some] at this
    exact (Point.some.inj this).2
  obtain ⟨x', rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hx
  obtain ⟨y', rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 hy
  have hns : (W.toAffine⁄Kv).Nonsingular x' y' :=
    (W.toAffine.baseChange_nonsingular (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv)).injective
      x' y').1 hxy
  exact ⟨Point.some _ _ hns, rfl⟩

/-- Points of $E(K_v)$ are fixed by $\operatorname{Gal}(\bar K_v/K_v)$. -/
theorem inclPoints_fixed (σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) (S : (W.toAffine⁄Kv).Point) :
    (localPointsRep Kv W).ρ σ (inclPoints W Kv S) = inclPoints W Kv S := by
  change Point.map (W' := W.toAffine) _ (Point.map (W' := W.toAffine) _ S) = _
  rw [Point.map_map]
  have : ((↑((AlgEquiv.restrictScalarsHom K) σ) : AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv).comp
      (IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv))) = IsScalarTower.toAlgHom K Kv (AlgebraicClosure Kv) :=
    AlgHom.ext fun a => σ.commutes a
  rw [this]

variable [W.IsElliptic]

/-- **Local injectivity from Kummer approximation**: if `KummerApprox W Kv n` holds for every $n \ge 1$, then
`LocalPointsInjectiveAt W Kv`. -/
theorem localPointsInjectiveAt_of_kummerApprox (h : ∀ n : ℕ, 0 < n → KummerApprox W Kv n) :
    LocalPointsInjectiveAt W Kv := by
  intro c hc hcob
  obtain ⟨Q, hQ⟩ := (mem_coboundaries₁_iff' _).1 hcob
  obtain ⟨n, hn, P, hP⟩ := exists_nsmul_eq_coboundary _ c hc
  let ι := localizePoints Kv W
  -- `nQ - ιP` is fixed
  have hfix : ∀ σ, (localPointsRep Kv W).ρ σ (n • Q - ι.hom P) = n • Q - ι.hom P := fun σ => by
    have h1 : ι.hom (n • c σ) = n • ((localPointsRep Kv W).ρ σ Q - Q) := by
      rw [map_nsmul, hQ σ]
    rw [hP σ, map_sub, Rep.hom_comm_apply ι σ P] at h1
    rw [map_sub, map_nsmul]
    rw [smul_sub] at h1
    have : (localPointsRep Kv W).ρ σ (ι.hom P) - ι.hom P =
        n • (localPointsRep Kv W).ρ σ Q - n • Q := h1
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact this.symm
  obtain ⟨R, hR⟩ := exists_inclPoints_of_forall_fixed W Kv _ hfix
  obtain ⟨S, T, hST⟩ := h n hn R
  -- `n (Q - S) = ι (P + T)`
  have hnV : n • (Q - inclPoints W Kv S) = Point.map (W' := W.toAffine) (closureEmb Kv) (P + T) := by
    rw [map_add]
    change n • (Q - inclPoints W Kv S) = ι.hom P + Point.map (W' := W.toAffine) (closureEmb Kv) T
    rw [hST] at hR
    rw [nsmul_sub]
    have := hR
    rw [eq_sub_iff_add_eq] at this
    rw [← this]
    abel
  obtain ⟨U, hU⟩ := exists_closureEmb_of_nsmul Kv W _ n hn _ hnV
  refine (mem_coboundaries₁_iff' _).2 ⟨U, fun σ => ?_⟩
  apply Point.map_injective (W' := W.toAffine) (f := closureEmb Kv)
  change ι.hom (_ - U) = ι.hom (c σ)
  rw [map_sub, Rep.hom_comm_apply ι σ U, ← hQ σ]
  change (localPointsRep Kv W).ρ σ (Point.map (W' := W.toAffine) (closureEmb Kv) U) -
    Point.map (W' := W.toAffine) (closureEmb Kv) U = _
  rw [hU, map_sub, inclPoints_fixed W Kv σ S]
  abel

end Reduction

end NumberFieldKB.MilneEC
