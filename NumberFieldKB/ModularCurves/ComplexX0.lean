import NumberFieldKB.ModularCurves.GenusX0
import NumberFieldKB.ModularCurves.Hecke

/-!
# The function field $\mathbb C(X_0(N))$ over $\mathbb C$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2–3 (pdf pp. 192–199). Corollary 3.4 compares weight 2
cusp forms with the holomorphic differentials of the compact Riemann surface $X_0(N)$, whose meromorphic functions are
$\mathbb C(j, j_N)$ (Theorem 2.3). This file builds the algebraic side over $\mathbb C$:

* `modPolyQC N`: $F_N$ with complex coefficients; it generates the ideal of $(j, j_N)$ in $\mathbb C[X][Y]$
  (`ker_evalJJNC_eq`), so it is irreducible (`irreducible_modPolyQC`), also over $\mathbb C(X)$;
* `X0C N` $= \mathbb C(X)[Y]/(F_N)$, a function field of one variable over $\mathbb C$ (`isFunctionField_X0C`) of
  degree $\mu = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$ over $\mathbb C(j)$ (`finrank_X0C`), with exact constant field
  $\mathbb C$ (`isIntegrallyClosedIn_X0C`, as $\mathbb C$ is algebraically closed);
* `toX0C N : X0 N →+* X0C N`, the inclusion $\mathbb Q(X_0(N)) \to \mathbb C(X_0(N))$ over $\mathbb Q(j) \to
  \mathbb C(j)$, sending $j \mapsto j$, $j_N \mapsto j_N$ (`toX0C_jX0`, `toX0C_jNX0`).
-/

open Polynomial

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ) [NeZero N]

/-- $F_N$ with complex coefficients. -/
def modPolyQC : ℂ[X][X] := (modPoly N).map (mapRingHom (algebraMap ℚ ℂ))

theorem modPolyQC_monic : (modPolyQC N).Monic := (modPoly_monic (N := N)).map _

theorem modPolyQC_natDegree : (modPolyQC N).natDegree = (CongruenceSubgroup.Gamma0 N).index := by
  rw [modPolyQC, (modPoly_monic (N := N)).natDegree_map, modPoly_natDegree]

/-- $F_N$ generates the ideal of $(j, j_N)$ in $\mathbb C[X][Y]$ (Proposition 2.4). -/
theorem ker_evalJJNC_eq : RingHom.ker (evalJJNC N) = Ideal.span {modPolyQC N} := by
  obtain ⟨-, -, hzero, hdiv⟩ := (prop2_4' N).exists_poly.choose_spec
  have hmap : ∀ G : ℂ[X][X], G.map (mapRingHom (RingHom.id ℂ)) = G := fun G => by
    rw [mapRingHom_id]; exact Polynomial.map_id
  ext G
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hG
    refine hdiv _ fun z => ?_
    rw [← hmap G, ← evalJJNHom_apply, hG]; rfl
  · rintro ⟨H, rfl⟩
    rw [map_mul]
    funext z
    simp only [Pi.mul_apply, Pi.zero_apply, evalJJNHom_apply, hmap]
    rw [show evalJJN N (modPolyQC N) z = 0 from hzero z, zero_mul]

/-- $F_N$ is irreducible in $\mathbb C[X][Y]$. -/
theorem irreducible_modPolyQC : Irreducible (modPolyQC N) := by
  have hp := isPrime_ker_evalJJNHom (N := N) (RingHom.id ℂ) (Nat.one_le_iff_ne_zero.2 (NeZero.ne N))
  rw [ker_evalJJNC_eq, Ideal.span_singleton_prime (modPolyQC_monic N).ne_zero] at hp
  exact hp.irreducible

/-- $F_N$ is irreducible over $\mathbb C(X)$ (Gauss's lemma; $F_N$ is monic). -/
theorem irreducible_modPolyQC_map : Irreducible ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ))) :=
  ((modPolyQC_monic N).irreducible_iff_irreducible_map_fraction_map).1 (irreducible_modPolyQC N)

/-- **The function field $\mathbb C(X_0(N)) = \mathbb C(X)[Y]/(F_N(X, Y))$** ($X$ is $j$, $Y$ is $j_N$). -/
@[kb "milne2006ec" "Ch. V, §2, the function field C(j, j_N) of X_0(N) over C (Thm. 2.3), pdf p. 192"]
abbrev X0C : Type := AdjoinRoot ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ)))

instance : Fact (Irreducible ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ)))) :=
  ⟨irreducible_modPolyQC_map N⟩

/-- Instance search does not find this one through `Field` (the ring structures of `AdjoinRoot` and of its field
structure agree only after unfolding). -/
instance : IsSimpleRing (X0C N) := DivisionRing.isSimpleRing (X0C N)

/-- $[\mathbb C(X_0(N)) : \mathbb C(j)] = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$. -/
theorem finrank_X0C : Module.finrank (RatFunc ℂ) (X0C N) = (CongruenceSubgroup.Gamma0 N).index := by
  rw [(AdjoinRoot.powerBasis (irreducible_modPolyQC_map N).ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    (modPolyQC_monic N).natDegree_map, modPolyQC_natDegree]

instance : FiniteDimensional (RatFunc ℂ) (X0C N) :=
  (AdjoinRoot.powerBasis (irreducible_modPolyQC_map N).ne_zero).finite

/-- $\mathbb C(X_0(N))$ is a function field of one variable over $\mathbb C$ (Tau Ceti's predicate). -/
theorem isFunctionField_X0C : TauCeti.IsFunctionField ℂ (X0C N) :=
  (TauCeti.IsFunctionField.ratFunc ℂ).finite_extension

/-- **$\mathbb C$ is the exact constant field of $\mathbb C(X_0(N))$** ($\mathbb C$ is algebraically closed). -/
theorem isIntegrallyClosedIn_X0C : IsIntegrallyClosedIn ℂ (X0C N) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨(algebraMap ℂ (X0C N)).injective, fun {x} hx => ?_⟩
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible (B := X0C N) hx)
  obtain ⟨c, hc⟩ := minpoly.degree_eq_one_iff.1 h1
  exact ⟨c, hc⟩

/-! ### The inclusion $\mathbb Q(X_0(N)) \to \mathbb C(X_0(N))$ -/

/-- $\mathbb Q[X] \to \mathbb C(X)$. -/
def polyQC : ℚ[X] →+* RatFunc ℂ := (algebraMap ℂ[X] (RatFunc ℂ)).comp (mapRingHom (algebraMap ℚ ℂ))

theorem polyQC_injective : Function.Injective polyQC :=
  (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
    (by rw [coe_mapRingHom]; exact map_injective _ (algebraMap ℚ ℂ).injective)

/-- $\mathbb Q(X) \to \mathbb C(X)$, $X \mapsto X$. -/
def ratFuncQC : RatFunc ℚ →+* RatFunc ℂ :=
  RatFunc.liftRingHom polyQC (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polyQC_injective)

theorem ratFuncQC_algebraMap (p : ℚ[X]) : ratFuncQC (algebraMap ℚ[X] (RatFunc ℚ) p) = polyQC p := by
  rw [ratFuncQC, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

theorem ratFuncQC_X : ratFuncQC RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncQC_algebraMap, polyQC]
  simp [RatFunc.algebraMap_X]

/-- The inclusion $\mathbb Q(X_0(N)) \to \mathbb C(X_0(N))$, over $\mathbb Q(j) \to \mathbb C(j)$. -/
def toX0C : X0 N →+* X0C N :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℂ) (X0C N)).comp ratFuncQC) (AdjoinRoot.root _) (by
    rw [Polynomial.eval₂_map]
    have h : ((algebraMap (RatFunc ℂ) (X0C N)).comp ratFuncQC).comp (algebraMap ℚ[X] (RatFunc ℚ)) =
        ((AdjoinRoot.of ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ)))).comp
          (algebraMap ℂ[X] (RatFunc ℂ))).comp (mapRingHom (algebraMap ℚ ℂ)) :=
      RingHom.ext fun p => by
        rw [RingHom.comp_apply, RingHom.comp_apply, ratFuncQC_algebraMap]
        rfl
    rw [h]
    have h2 := AdjoinRoot.eval₂_root ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ)))
    rw [modPolyQC, Polynomial.eval₂_map, Polynomial.eval₂_map] at h2
    exact h2)

theorem toX0C_algebraMap (x : RatFunc ℚ) :
    toX0C N (algebraMap (RatFunc ℚ) (X0 N) x) = algebraMap (RatFunc ℂ) (X0C N) (ratFuncQC x) := by
  rw [AdjoinRoot.algebraMap_eq, toX0C, AdjoinRoot.lift_of]
  rfl

theorem toX0C_root : toX0C N (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.lift_root _

theorem toX0C_jX0 : toX0C N (jX0 (prop2_4' N)) = algebraMap (RatFunc ℂ) (X0C N) RatFunc.X := by
  rw [← algebraMap_X_X0, toX0C_algebraMap, ratFuncQC_X]

theorem toX0C_jNX0 : toX0C N (jNX0 (prop2_4' N)) = AdjoinRoot.root _ := by
  rw [jNX0, coordToX0_mk, Polynomial.map_X, AdjoinRoot.mk_X, toX0C_root]

end NumberFieldKB.ModularCurves
